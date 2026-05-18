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

263 total modules (`cabal run shake -- count-modules`):
- **258**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer — co-located here to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

262 of 263 modules use `--safe`. No modules require `--sized-types`. Per-commit module-count drift (Path A.4 cluster lift, Track E sub-phase additions, R18 cluster 14 extraction, R18 cluster 2 `Aletheia.Limits` extraction, R19 Phase 2 cluster 8 `Aletheia.DBC.Formatter.Bounded` extraction, R20 cluster V `Aletheia.DBC.BoundWalks` extraction, R20 cluster Y stage 2 `Aletheia.DBC.RationalRenderer` (+`.Properties`) lift, R21 cluster 9 `DecRatParse/Properties` split into 5 phase submodules, R21 cluster 9 follow-up `Properties/Primitives` split into MuxMarker + Bools sibling submodules at `543acee`, R21 cluster 9 follow-up `Format` split into `Format/RegressionTests` sibling at `000761b`, R21 cluster 9 follow-up `Format/AttrDef` split into `Format/AttrDef/HeadHelpers` at `9421604`, R21 cluster 9 follow-up `Aggregator/Dispatcher/Attribute/Assign` split into `Assign/Bridges` at `9c7740d`, R21 cluster 9 follow-up `Refine/ValueDescriptions` split into `ValueDescriptions/UnresolvedRVDs` at `627ad25`, R21 cluster 9 follow-up `Properties/Attributes/Line` split into `Line/Alt5` at `5b48948`, R22 AGDA-D-15.1 final closure `Format/AttrLine` split into `Format/AttrLine/Builders` at `0b360fd`, etc.) is recorded in PROJECT_STATUS.md and `memory/project_b3d_universal_proof.md` / `memory/project_track_e_val_promotion.md` / `memory/project_review_round18.md` / `memory/project_smart_rational_renderer.md` / `memory/project_review_round21.md`.

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

For full history (R6–R19, Path G, Phase 5.1, Tracks A–E, B.3.d Layers 1–4) see [PROJECT_STATUS.md](PROJECT_STATUS.md). Per-commit narratives + sub-phase tactical detail live in PROJECT_STATUS.md and the `memory/project_*.md` files indexed in `MEMORY.md`. Resume notes / next-session entry point: [.session-state.md](.session-state.md).

**Active branch: `review-r22`** — forked from `main` post-R21 merge (`315c1a3` 2026-05-18; R21 merge fork point `e3107f6`).  Module count **263** (unchanged from R21 close; R22 work to date is dead-import prune only — no module structure changes).  R21 review round MERGED to main via `315c1a3` (`--no-ff`); R21 narrative + 14-cluster commit index in `memory/project_review_round21.md`.  Live commit count: `git rev-list --count main..HEAD` per `feedback_self_referential_count_drift.md`.

**R21 round** (2026-05-17): 14 clusters initial pass + user-directed closure on the 5 DEFERs.  Initial pass: 17 agents → 241 finding bullets; 9 HIGH items closed + 4 cross-binding HIGH; 5 DEFERs with in-source markers.  User-directed closure: "fix all 5 items" → 3 fully CLOSED (D-12.1 walker+bindings, SYS-32.2 UBSan-on, D-13.2 correction), 2 PARTIAL (A-1.1 ~29% via 6 dead-import batches; D-15.1 1of8 via DecRatParse split chain).  Cluster commit index:

- Initial pass (clusters 1-14): `df533e7` · `2fde107` · `d41d6d3` · `7e3b035` (cluster 5 was Excel rational scale, then closure cluster 4 = `b296c34` was `BatchExtraction.formatBounds`) · `cb96c39` · `616cef1` (DEFER cluster 7 = AGDA-D-12.1) · `013f5c4` · `6210872` (DEFER cluster 9 = AGDA-D-15.1) · `3ed5bb4` · `7cd017e` · `2be48fd` · `b611250` · `e3cbea0` · `12ce99a` (DEFER cluster 14 = SYS-32.2)
- User-directed closures (chronological): **R21 cluster 14 flip** `3498782` (UBSan opt-in → always-on; `--san`/`OptInOptions` removed; BASE_STEPS 27→29) · **cluster 9 split chain** `d02c955` (phase 1) → `420f32b` (phase 2) → `8d31d35` (phase 3) → `33574c9` (phases 4-6 facade) → `b5bd988` (Phase4Composition fixup missing from `33574c9` git add) · **cluster 9 AttrLine update** `42824a9` (DEFER refresh after split blocker found — empirical investigation captured) · **cluster 10 batches** `d4114b9` (1) → `98b2e18` (2) → `481041f` (1 residuals) → `3e70068` (3) → `bb29da6` (4) → `bf1146d` (5) → `13cdd07` (6); ~250 of 864 candidates resolved via scanner v2.2 (allowlist `-syntax` + mixfix `_X_` strip + top-level-only import boundary; ~5% false-positive rate caught by per-file `agda --type-check` verify) · **cluster 5 closure** `0f8f831` (AGDA-D-13.2 corrected; finding misread the signature — Metric* already carries `Timestamp μs` window bound; second ℕ is suc-encoded `startTime` sentinel) · **cluster 1 closure** `85623b7` (wire scaffold: `WarningKind`+`Warning` ADTs + `Response.Complete` extension + JSON serializer; binding parsers tolerate via `warnings:[]`) → `afd28f3` (walker `collectUncachedWarnings` in `Protocol.Handlers` + 3 binding decoders `Python CompleteWarning`/`Go StreamWarning`/`C++ StreamWarning` + test trio per binding + feature matrix row `end_stream_uncached_atom_warnings`) → `1e53080` (`signalOf` `Types.public` re-export — `WarmCache.agda` was importing from the Properties module the lift removed) → `dd8bb81` (CHANGELOG entry per UR-1).

**R22 A-1.1 batches 7-23 (2026-05-18 → 2026-05-19)** — batches 7-9 landed on `review-r21` pre-merge; batches 10-23 on `review-r22` post-merge.  Per-batch narrative + commit hashes consolidated in `memory/project_review_round21.md`; summary:

- **b7-b18** (mid-density tier, 60 files / ~480 candidates): lessons distilled along the way — `feedback_qualified_access_empty_using.md` (b10), `feedback_public_reexport_blindspot.md` (b14, scanner v2.4 `public`-line skip), Assign.agda R22-PRE-CLOSE side-observation (b15).
- **b19** `da0b881` (5f / 35c — new lesson `feedback_grep_E_word_boundary.md`).
- **b20** `dfa6937` (5f / 42c / 1 FP `⌊_⌋` — scanner v2.5 rebuilt after WSL restart; new lesson `feedback_unicode_brackets_scanner.md`).
- **b21** `3acda42` (5f / ~73c — Network.agda 15 FN via per-name `grep -cP`; new lesson `feedback_scanner_fn_audit_heavy_imports.md`).
- **b22** `3849884` (5f / ~131c — Bridges + Refine + Common + Line + Primitives; b21 FN-audit re-applied catching 7 more FNs; 2 scanner FPs retained `-[1+_]`/`⌊_⌋`; Line's 15 `parseRawAttrAssign-roundtrip-ATgt*-Rav*` + 5 module aliases were AGDA-D-15.1 split residuals).
- **b23** `0be1ca3` (5f / ~228c — DecRat tier: DecRat + RationalRoundtrip + Phase3Naturals + Phase4Composition + Phase6Suffix; scanner v2.5 → v2.6 multi-line `using\n  (...)` fix caught the Refinement clause across Phase4/Phase6 that v2.5 missed entirely; 1 mid-batch over-prune-and-restore (`∣_∣` in DecRat L57 broken by L210 `IsCanonical ∣ numerator ∣` use, caught by per-file agda); new lesson `feedback_scanner_fn_mixfix_with_args.md`).
- **b23 simplify follow-up** `3e63ca3` (5f / 10c — surfaced by `simplify` skill's quality-review agent: scanner doesn't process `renaming (...)` at all + line-granularity within `using (...)`; items spanned `↥_ to ↥ᵘ_; ↧_ to ↧ᵘ_` renames + `_++ₗ_` rename + `cong` (only `cong₂` used) + `DecRat` type inferred from `mkDecRat` ctor).

**Cumulative R21/R22 A-1.1 closure: 105 files / ~1195 candidates** (past original 864 estimate per b21+b22+b23 FN catches).  Scanner v2.6 at `/tmp/scan_dead_imports.py` (no backup — rebuild from `feedback_unicode_brackets_scanner.md` notes + b23 multi-line fix if WSL restarts).  Known scanner FPs: (1) Unicode-bracket mixfix `⌊_⌋`/`⌈_⌉`/`-[1+_]` outside ident class (per-file agda catches); (2) mixfix-with-token-collision (`+_` vs `++`, `if_then_else_` body tokens — context-dependent); (3) `public` re-exports (v2.4 line-skip).  **Known FN classes** (b21-b23): heavy `using (...)` clauses (combinator families, PropEq sets), `import M as N` module aliases (qualified `N.X` not tracked), multi-line `using\n  (` (v2.5 → v2.6 fix), `_X_` mixfix-with-args (`∣_∣`, `ifᵀ_then_else_`, `-[1+_]`, `_≈ᵇ_` — body usage scatters tokens around args), `module X` literal (body uses `X.field` / `open X`), `renaming (X to Y)` clauses (scanner doesn't process at all).  **Workflow**: per-name `grep -cP` audit after scanner pass + `simplify` skill quality-review agent post-prune (catches residual `renaming` + within-using-clause items).

**Gates fresh at `3e63ca3`** (R22 A-1.1 batch 23 simplify follow-up landing, 2026-05-19): build clean **3m53s** / check-properties clean **14m47s** "All proof modules type-checked successfully" / count-modules **263** (unchanged).  Three prior check-properties passes within b23: 13m02s (first pass) + 13m07s (second pass after first-round residuals) + 14m47s (simplify follow-up).  Other invariant gates NOT re-run for b23 — only structural changes flip them, none here.  Binding tests NOT re-run — dead-import pruning is MAlonzo-neutral.  Prior `5e01ce3` benchmark posture (R20 R6-B7.4 baseline) remains the last refreshed empirical baseline.

**Next**: continue AGDA-A-1.1 — high-density tiers (R22-original and DecRat) both CLEARED; only `Aggregator/Dispatcher/Attribute/Assign.agda` (28 per v2.5) remains, but it overlaps with the R22-PRE-CLOSE blocker so prune side-by-side with stale-re-export fix.  Mid-density (10-20) and long-tail (<10) tiers need re-scan with v2.6 — pre-b23 estimates may be stale.  **AGDA-D-12.1 follow-ups REQUIRED** (re-labeled 2026-05-19 at `d2326a4` per user directive; in-source block at `Adequacy/StreamingWarm.agda:392-406`): per-warning `LogEvent.endstream.uncached_atom` enumerant + cross-binding parity, `check-runbook` entry, PROTOCOL.md warnings-field write-up — three items, must land before next review round's close.  **Pre-close blocker** (b15 side-observation + `74a72fa` in-source marker): 18 pre-existing `ModuleDoesntExport` warnings in `DBC/TextParser/Properties/Attributes/Assign.agda:35-65` — stale `using (...)` re-exports of submodule names.  Must be resolved before R22 → main merge — see in-source `R22-PRE-CLOSE` block.  **Push gap**: local `main` 152 commits ahead of `origin/main` — R20+R21 merges held local per `feedback_review_branch_workflow.md`.

**R20 round** (2026-05-12 → 2026-05-17, end-of-round DEFER queue further reduced — R6-B7.3 + R6-B7.4 closed via lift + parameterisation) — 17 agents → 671 raw findings (`3571702`); split (`3fa8e65`) into Clusters A-V + DEFER-end-of-round; W/X/Y/GO-A-3.5 closed pass-2; nine user-redirected closures post-Y. Cluster commit index:

- A `4be9a84` · B `dbd3e60` · C `c2c6bab` · D `9a73a48` · E `c795141` · F `036a684` · G `00dc764` · H `ea62e60` · I `33d0e44`(+`ba1f005`) · J `efa041f` · K `ee76e91` · L `eb597f9` · M `11f4100` · N `d5f28b8`(+`f39de48`) · O `8bb0055`(+`78dcda5`) · P `4dd3c05`(+`ac202e6`) · Q `e15bd6d` · R `10a07d6` · S `637b2e0`(+`d838fa5`) · T `a1fe3fe` · U `7fc7b0b` · V `6e8afc9` · W `c40e3ba` (`StepOutcome` Satisfied→complete soundness — see `project_classify_satisfied_soundness_gap.md`) · X `83ad17a` (C++ `Strong<Tag,T>` unification + `LtlFormula` variant-by-composition) · GO-A-3.5 `b77ec3a` (cross-binding `MuxValues` → `MultiplexValues` rename) · Y `c6a7e73`+`a632b63`+`c3b4092`+`16901e7`+`57f8d44`+`718404b`+`fb43d71`+`cbd631f`+`1f8771b` (Rational renderer lifted into Agda kernel; lazy-load FFI in all 3 bindings; advisor caught fallback in Go/C++ stage-2 cutovers; new feedback `feedback_no_local_fallback_alongside_ssot.md`; detail in `project_smart_rational_renderer.md`).
- Post-Y user redirects (chronological): **Phase C1** `92e7eaa` (Metric* lift ℕ → `Timestamp μs`; audit-trail flips R5-A11 / R6-P1.1 / R6-B9.1 / R6-B7.3) · **R20-GO-A-4.10** `7cb131a` (new `tools/check_limits_parity.py` gate; `run_ci.py` step count 27→28) · **R5-B1 + R6-B7.1** `aa308c8` + `35e306f` (LE bitLength=0 → parse error across both parse surfaces; new feedback `feedback_test_guard_parameterise_over_diff.md`) · **R20-AGDA-B-26.3 + GA9.1** `f478bb5` (`injectHelper` lifted + Bool fast-path via stdlib `Reflects` two-with form; reproducer at `/tmp/agda-with-in-eq-repro/MinimalRepro.agda`; revises `feedback_with_in_eq_outer_abstraction_barrier.md`) · **R6-B8.2** `970f704` (`sound-or` derived from `sound-and` via De Morgan; net −161 LOC; new `feedback_nofix_rationale_incomplete_axis.md`) · **test-hygiene** `823c69b` (3 pre-existing lint findings + new `feedback_use_venv_for_gates.md`) · **R20-AGDA-C-27.1 audit** `e6bbb31` (DEFER → FIX → revert + DROP after empirical 5.69× regression measurement on `parseDBCText` path; 24-line in-source DO-NOT-RE-RAISE block + new `feedback_stdlib_equivalence_vs_expansion.md`) · **R5-C2 / R6-B8.1 / R6-B8.2 sound-and / R20-AGDA-B-18.3 audit** `4e88574` (in-source DO-NOT-RE-RAISE blocks for 4 stable NO-FIX items) · **R6-B7.3 FIX** `7d35b6c` (`CachedSignal.lastObserved : ℕ → Timestamp μs` lift across 7 files) · **R6-B7.4 FIX** `5e01ce3` (`PropertyState n` parameterised with `Fin n` index; `Data.Fin.toℕ` only at wire boundary; 8 Agda + 3 haskell-shim files; perf-neutral on per-frame Continue path; distinct from `Internals.agda` 98-136 `Fin (length atoms)` hot-path warning) · **UPD size budget** `188e664` (UPD shorthand extended with 40.0 kB CLAUDE.md size budget check; compression in same commit if over) · **final pre-merge audit** `3194ea4` (in-source DO-NOT-RE-RAISE blocks for the last 3 weak-coverage items: R20-AGDA-D-19.3/D-GA20.1 `nothing≢just` in `StreamingWarm.agda`, R20-GO-A-3.6 `StandardID`/typedef asymmetry in `go/aletheia/types.go`, R20-GO-A-3.7 lockCh/closeOnce split in `go/aletheia/client.go`; comment-only across 4 files; every open R20 item now has durable in-source justification).

WSL2 jitter empirical 2026-05-12: median 1.70%, max 4.58% inter-batch CV (`feedback_wsl2_variance_stance.md`).

**Next**: `--no-ff` merge of `review-r20` to `main` per R18/R19 precedent. End-of-round DEFER queue empty; every DEFER/DROP/FP-VERIFIED/NO-FIX item carries an in-source `DEFER` / `DO NOT RE-RAISE IN REVIEW` block visible at the call site. **DEFERRALS.md retired 2026-05-17** — review carry-over now reads in-source markers (canonical) + the round's `review-rN-findings.md` (working file).  10 R19 Phase 2 cluster 10 / 16 scope-deferrals were the last items lacking in-source markers; all migrated via `R19P2-CL10-N` / `R19P2-CL16-N` referent comments.

**Gates fresh at `5e01ce3`** (R6-B7.4 architectural FIX commit, 2026-05-17): 12 Agda gates clean (build 1m46s / check-properties 8m28s / check-invariants / check-no-properties-in-runtime / check-erasure 1m45s / check-fidelity 17/17 / check-ffi-exports 45 entries / check-bound-enforcement 7 BoundKind ctors / count-modules 250 / check-runbook 15 events / check-changelog / check-limits-parity 14+7 in parity); pytest **866p+1s** in 5.93s (venv); Go test -race ok 8.549s; C++ ctest 10/10 (24.66s). R6-B7.3/R6-B7.4 are both runtime-shape changes (`CachedSignal.lastObserved : ℕ → Timestamp μs`; `PropertyState.index : ℕ → Fin n`) — first is per-frame on `handleDataFrame`'s cache-update path (one `timestampℕ` unwrap eliminated, no MAlonzo cost change since `Timestamp μs` compiles to the same `Integer` as `ℕ` via `@0 u : TimeUnit` erasure); second is wire-only (per-property identifier reaches `PropertyResult.Violation/Satisfaction/Unresolved` via single `toℕ` at emit, no per-frame impact on the `Continue` path). Benchmarks deferred to next session unless user requests — both changes are within the WSL2 session-distant ±10% band on first-principles analysis.  Prior `823c69b` benchmark posture (10000 frames × 5 runs × 3 bindings: 18/18 lanes within ±10% WSL2 band; max favorable +9.8% C++ Stream LTL 2.0B σ=3.7%; max regression −7.4% Go CAN-FD Stream LTL σ=7.8%) was the last refreshed baseline.

**Prior tracks**:
- **R19 Phase 2** ✅ MERGED via `41f6ba6` 2026-05-12 + tidy `2e79ed8`; pushed. 17 agents → 19 clusters all closed; carry-over phase ✅ 2026-05-09 (9/9 R18 carry-overs; R19-CARRY-1 partial RE-DEFER). Detail: `memory/project_review_round19.md`.
- **R18** ✅ merged via `4518fef` 2026-05-09; 17 hard clusters + benchmarks/ promotion; 112 hard findings cumulative. Detail: `memory/project_review_round18.md`.
- **Cluster 8 + Phase 2b** ✅ 2026-05-11 — defense-in-depth bound checks at parser surfaces; Phase 2c shipped 2026-05-13 in R20 cluster I. Lessons: `feedback_handler_vs_parser_bound_placement.md`, `feedback_parsedbc_quadratic_scaling.md`.
- **Memory-bound build infra** `43fcd4b` 2026-05-11 — `cabal build -j16 --ghc-options="+RTS -A64M -M3G -RTS"`. Lesson: `feedback_parallel_memory_budget.md`.

**Standard gates passed at every closure** — `cabal run shake -- {build, check-properties, check-invariants, check-no-properties-in-runtime, check-erasure, check-fidelity, check-ffi-exports, check-bound-enforcement, count-modules, check-runbook, check-changelog, check-limits-parity}` + Python `pytest tests/` + Go `go test ./aletheia/ -race` + C++ `ctest --test-dir cpp/build` + lint gates. Per-closure gate logs live in PROJECT_STATUS.md.

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
