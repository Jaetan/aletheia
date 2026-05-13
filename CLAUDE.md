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

For full history (R6–R18, Path G, Phase 5.1, Tracks A–E, B.3.d Layers 1–4) see [PROJECT_STATUS.md](PROJECT_STATUS.md). Per-commit narratives + sub-phase tactical detail live in PROJECT_STATUS.md and the `memory/project_*.md` files indexed in `MEMORY.md`. Resume notes / next-session entry point: [.session-state.md](.session-state.md).

**Active branch (2026-05-13): `review-r20`** — R20 review round in progress. Forked from `main` at `2e79ed8` 2026-05-12 (post R19 merge `41f6ba6` + post-merge tidy `2e79ed8` removing R18/R19 findings files; pushed to remote). Live count via `git rev-list --count main..HEAD` per `feedback_self_referential_count_drift.md` (20 commits on branch as of cluster K + this UPD doc-sync). Module count **247** (R20 cluster H added 3 new `Aletheia.Limits` bound constants — `max-comments-per-file`, `max-nodes-per-file`, `max-value-tables-per-file`; cluster I extended JSONParser/Routing/Handlers/MetadataRoundtrip cascade `ParseError ⊎` → `Error ⊎` + added `tools/check_bound_enforcement.py`; cluster K added new C++ `AletheiaException` class to `cpp/include/aletheia/error.hpp`; no new Agda modules — all extensions in place). Python module count from R19 cluster 17 carries forward (+2 from protocols.py split + PY-D-20.3 cli.py layering inversion; validation.py rename net 0).

**R20 review round** (started 2026-05-12) — 17 review agents → **671 raw findings** seeded as `3571702`; cluster split saved as `3fa8e65` into Clusters A-R + DEFER-end-of-round.  **Clusters A-K ✅ CLOSED + regen safety fix** (cumulative 11 fix commits + 1 follow-up + 2 setup + 3 docs + this UPD = 20 commits on branch).  Cluster A `4be9a84` (conftest.py `ProcessError` unblock — PY-A-1.1 / PY-D-27.1; doc-example harness gate was RED).  Cluster B `dbd3e60` (Go build matrix — `ffi_nocgo.go` SendFrameBinary 7-arg stub + compile-time Backend interface assertions; `CGO_ENABLED=0 go build` clean).  Cluster C `c2c6bab` (cross-binding rational discipline — Go `math/big.Int` cross-product `rationalLess` replacing int64-overflow-prone multiply, Python `<= 0` denominator reject, C++ `INT64_MIN` guard).  Cluster D `9a73a48` (C++ CPP-D-22.1 — `send_frames` mid-batch error wrap forwards `e.bound_info()` to preserve structured `bound_kind/observed/limit` triple).  Cluster E `c795141` (docs hygiene sweep — module/test counts, Python 3.13 floor synced × 5 sites, Last-Updated stamps).  Cluster F `036a684` (BRS/ESI mock fidelity — `serialize_send_frame` + `serializeDataFrame` extended, MockBackend / IBackend / Backend interfaces threaded; 9-combination cross-binding parity tests).  Cluster G `00dc764` (CHANGELOG R19 BREAKING sections × 4 — Python `ProcessError` removal, Go `Dbc*`→`DBC*` rename, Go predicate `float64`→`Rational`, Go SendFrame BRS/ESI args; cpp/README Quick-start rebuilt for `AletheiaClient` + `stop_token{}`; go/README SendFrame 7-arg; CANCELLATION.md Go + C++ signatures gain BRS/ESI).  Cluster H `ea62e60` (FIX-NOW + universal-rule cardinality gaps — AGDA-D-11.2 / AGDA-D-32.4 `firstDBCOverBound` extended with 4 new cardinality checks `comments` / `nodes` / `valueTables` / `totalValueDescriptions`; 3 new bound constants in `Aletheia.Limits`; GO-B-12.1 `parseRational` defenses; 5 new Go reject tests; stragglers bundled per `feedback_gate_claim_integrity.md`).  **Cluster I `33d0e44`** (BoundKind enforcement audit + FFI snapshot constructor coverage — AGDA-D-32.1 IdentifierLength: `validateIdent` body split on `T? (validIdentifierᵇ cs)` first, then on length for the `no` branch — length-overflow emits `Error.InputBoundExceeded IdentifierLength obs limit`, grammar-invalid stays `ParseErr (InvalidIdentifier name)`; JSONParser return-type cascade `ParseError ⊎` → `Error ⊎` across ~40 fn signatures; 27 `inj₁ <ParseError ctor>` sites wrapped with `ParseErr`; 63 `require (<ParseError ctor>)` sites wrapped with `require (ParseErr <ctor>)`; `addSignalContext` switched from `mapₑ (InContext ctx)` to `mapₑ (WithContext ctx)`; `parseDBCWithErrors` lifts to `Error ⊎ DBC`; `Handlers.withParsedDBC` + `Handlers/FormatDBCText.handleFormatDBCText` updated to unwrap Error directly, dropping the `HandlerErr (WrappedParse parseErr)` envelope. — 32.2 StringLength: post-parse handler walk over every unbounded `List Char` field (DBC.version / per-signal unit + valueDescriptions / comments / attribute names + AVString + ATEnum labels / value-table labels / unresolved value-desc labels) emits `InputBoundExceeded StringLength` at the handler boundary, mirrored in `Handlers.agda` + `Handlers/ParseDBCText.agda`. — 32.3 FrameByteCount: `Routing.parseBytePayload` pre-check on `length byteList > max-frame-byte-count` BEFORE `listToVec`; Routing cascade `RouteError ⊎` → `Error ⊎` on all try* functions + `dispatchCommand` + `parseCommand`; internal helpers stay RouteError-typed and bridge via `mapₑ RouteErr`; binary FFI mirror via new `FFIError` ADT in `AletheiaFFI/Marshal.hs` rendered byte-for-byte against Agda's `responseToJSON` envelope (4 binary FFI call sites updated). — 32.5 Shake gate: new `check-bound-enforcement` phony + `tools/check_bound_enforcement.py` parses `data BoundKind` and greps for `InputBoundExceeded <Ctor>` emit sites under `src/`; all 7 ctors have ≥ 1 emit site. — 30.1 snapshot constructors: `haskell-shim/ffi-exports.snapshot` extended with `F:` / `C:` / `T:` mode markers; `check-ffi-exports` parses the prefix and dispatches per kind; 44 entries = 19 functions + 14 constructors + 11 types pinning every load-bearing MAlonzo type/ctor the Haskell shim unsafe-coerces through).  **Cluster I safety fix `ba1f005`** (advisor-flagged follow-up — `regen-ffi-exports` iterated only `ffiExports` and overwrote the whole snapshot, would have wiped all 14 C: + 11 T: + 8 indirect F: lines on next post-cluster-I run; new regen reads existing snapshot, refreshes F: NN suffix in-place for ffiExports matches, preserves all other lines verbatim; idempotent against current snapshot; `length c \`seq\` return c` forces strict read before writeFile to avoid lazy-IO lock; lesson saved as `memory/feedback_regen_tool_preservation.md`).  All 47 cluster-A-G FIX marks + 5 cluster-H FIX marks + 5 cluster-I FIX marks + 4 cluster-J FIX marks + 2 cluster-K FIX marks logged in `review-r20-findings.md`.  **WSL2 jitter** measured empirically 2026-05-12: median 1.70%, max 4.58% inter-batch CV; ±10% reference retained for session-distant comparisons (`feedback_wsl2_variance_stance.md`).  Per-cluster commit hashes + scope: `memory/project_review_round20.md`.  Gates run fresh at every cluster ship: cluster I adds `check-bound-enforcement` to the standard sweep → **9 Agda gates clean** (build + check-properties / check-invariants / check-no-properties-in-runtime / check-erasure / check-fidelity / check-ffi-exports / check-bound-enforcement / count-modules / check-runbook); Python pytest **825p+1s** post-cluster-J (collection growth from test additions earlier in the round); Go test -race ok; C++ ctest 10/10; basedpyright `aletheia/` 0/0/0; pylint 10.00/10; gofmt + go vet + clang-format + clang-tidy clean.  **Cluster J `efa041f`** (Python `ValidationError` migration — PY-A-5.3 / PY-B-8.1 / PY-B-8.4 / PY-D-27.3; all ~58 production `raise ValueError(...)` sites under `python/aletheia/` migrated to `raise ValidationError(...)` across 13 modules — `_types.py`/`_enrichment.py`/`_helpers.py`/`dsl.py`/`checks.py`/`_check_conditions.py`/`checks_runner.py`/`_loader_utils.py`/`excel_loader.py`/`yaml_loader.py`/`dbc_converter.py`/`can_log.py`/`cli.py`; 30+ `pytest.raises(ValueError, …)` swapped across 12 test files; classification audit (pre-edit advisor consult) confirmed every site is caller-validation — `_enrichment.py` depth bound on user-supplied DSL formulas → `ValidationError` not `InputBoundExceededError` (kernel isn't the emitter), `_helpers.py` rational helpers called from `_client.send_frame`'s `coerce_to_rational` on user values → `ValidationError` not `ProtocolError`; stdlib `except ValueError:` catches around `int()` / `Fraction()` / `bytearray.fromhex()` / `Enum(code)` / `json.loads` preserved as control flow; `test_batch.py` mock injections stay `ValueError` (BatchError wraps arbitrary, mock placeholder); **circular-import fix**: `_loader_utils.py` uses direct `from .client._types import ValidationError` path with in-source comment to dodge the `client/__init__.py` partial-initialization cycle when loaded transitively from `_helpers.py` — `_types.py` finishes loading earlier in the chain so the explicit submodule import resolves cleanly; **production fallthrough fix caught by pytest**: `cli.py:556` `except ValueError` around `parse_can_id` in `_resolve_mux_message` lifted to `except ValidationError` (mux-query name-fallback path regressed under pytest at `Invalid CAN ID: 'DiagStatus'`); generalizable lesson saved as `memory/feedback_exception_class_migration_audit_catches.md` (production `except <OldExc>:` blocks around helpers being migrated to raise `<NewExc>` are silent regressions waiting to happen — grep alongside `raise <OldExc>` sites up front); bench gate skipped per advisor since exception-class swap touches only the error path).  **Cluster K `ee76e91`** (C++ `ErrorKind::Ffi` emission + `AletheiaException` wrapper — CPP-D-21.4 / CPP-B-7.3; the enum kind was declared in error.hpp since R19 but never constructed).  New `AletheiaException` class in `cpp/include/aletheia/error.hpp` deriving from `std::runtime_error`, holds an `AletheiaError`, exposes `kind()` / `code()` / `error()`.  Existing `catch (const std::exception&)` blocks keep catching it via the base; new code can `catch (const AletheiaException&)` to recover the kind tag.  6 throw sites migrated from `std::runtime_error`: `dlopen` failure (FfiBackend ctor) + `dlsym failed for <name>` (load_sym) + `aletheia_init() → null` (AletheiaClient ctor at client.cpp:69) → `ErrorKind::Ffi`; runtime `aletheia_*() → null` via `wrap_str_result` 8 call sites → `ErrorKind::Protocol` (matches Python `ProtocolError` at _client.py:231/245 — boundary loaded successfully, kernel just produced no response; narrow Ffi semantics per error.hpp:18 enum docstring); `rts_cores < 1` (caller-argument rejection) + payload `data.size() > max_can_fd_payload_bytes` (mirrors sibling `update_frame_bin` / `extract_signals_bin` Result paths at lines 372/397) → `ErrorKind::Validation`.  Catch-site update at `apply_checks` (client.cpp:493) — `AletheiaException` caught BEFORE `std::exception` so kind isn't silently downgraded to `Validation` (advisor's lock-#1 to do BEFORE migration; otherwise new kinds get silently downgraded by the prior `Validation`-everything catch).  JSON-fallback catch at `extract_signals_internal` keeps single `std::exception&` catch (symmetric with binary-path `log + nullopt for any kind != BinaryUnsupported` convention at lines 850-855; advisor reconciled "rethrow Ffi" to "keep log+swallow symmetry" because the function returns `std::optional<>` not `Result<>`).  Initial draft added a `kind` field to the `extraction.process_failed` log warn but advisor flagged cross-binding parity break — Python/Go don't emit kind on this event; removed.  3 new Catch2 tests in `cpp/tests/unit_tests_validation.cpp`: bad lib path → `AletheiaException` with `kind() == ErrorKind::Ffi`, `rts_cores=0` → `AletheiaException` with `kind() == ErrorKind::Validation`, `AletheiaException` catchable as `std::exception` (transition guarantee).  CHANGELOG.md gains a C++ Added entry under `[2.0.0] — Unreleased`.  Two `<stdexcept>` include-cleaner removals (client.cpp + ffi_backend.cpp) — `AletheiaException` provides the throw class transitively via `<aletheia/error.hpp>` / `<aletheia/backend.hpp>`.  Bench gate skipped per advisor (error-path-only changes).  Next: Cluster L (BRS/ESI doc-fence sweep — closes 102 fence failures from cluster A unblock; CANFrameTuple is 7-tuple post R19 cluster 18, docs still unpack 5).

**R19 Phase 2 ✅ MERGED to main** via `41f6ba6` (`--no-ff`) 2026-05-12; post-merge tidy `2e79ed8` removed R18/R19 findings files; pushed to remote.  Phase 2 was 17 review agents → 19 clusters; **19 of 19 closed** (7 FIX-early + 8 FIX-middle + cluster 14 closed 2026-05-12 + cluster 17 ✅ CLOSED 2026-05-12 + cluster 18 ✅ CLOSED 2026-05-12 EOD + cluster 19 ✅ CLOSED 2026-05-12 `b36177c`). Per-cluster commit hashes + scope: `memory/project_review_round19.md`. **Cluster 19 ✅ CLOSED 2026-05-12** — hot-path allocations across bindings, single commit `b36177c` (originally DEFER-end-of-round; user-directed engagement, 4 sub-findings FIX + 1 design-held with in-source DEFER rationale): **PY-B-14.2** hoist `(_ACK_BYTES, _ACK_BYTES_SPACED)` to class const `_ACK_RESPONSES` (3 streaming-hot membership tests no longer rebuild the 2-tuple per frame); **PY-B-10.3 / PY-D-22.5** three sites (`_client.py:_call_send_frame_ffi`, `_signal_ops.py:extract_signals`, `_signal_ops.py:update_frame`) switch `(c_uint8 * N)(*data)` → `(c_uint8 * N).from_buffer_copy(data)` (single C-level memcpy vs O(N) Python-level per-byte coercion); **PY-B-14.1** three `LogEvent.FRAME_PROCESSED` callsites in `send_frame` gain outer `if _logger.isEnabledFor(logging.DEBUG):` guards mirroring stdlib's `Logger.debug` fast path; **CPP-B-25.1** `last_frames_` map replaces `insert_or_assign(... FramePayload(b,e))` with `find`-then-`assign` (existing key) / `emplace` (new key) — reuses the existing `FramePayload`'s vector capacity on subsequent frames for the same CAN ID; header comment claiming "one FramePayload copy per unique CAN ID (not per frame)" was wrong on the per-frame side — comment now reflects actual cost. **GO-B-25.2** design-held with in-source DEFER comment: `serializeDataFrame` `sync.Pool` candidate verified mock-backend / test-only via `grep -rn` (real streaming uses binary FFI `sendFrameBinary`). Bench (post-cluster-18 → cluster-19, runs={5,5} × 10000 frames, two-batch noise diagnostic per `feedback_benchmark_noise_diagnostics.md`): touched Python streaming-hot lanes show credible directional wins — Stream LTL CAN 2.0B +10.05%, Stream LTL CAN-FD +12.14%, Signal Ext CAN 2.0B +6.24%; untouched lanes (C++ all lanes -5 to -13%, Python build_frame -10%) show host-side WSL2 noise rather than code regression (Go flat ±2% across identical change set + same-binary A→B variance up to +5.79% on C++ confirms noise envelope).  All gates clean.  Module count unchanged at 247.  **Cluster 18 ✅ CLOSED 2026-05-12 EOD** — BRS/ESI cross-binding plumbing (AGDA-D-10.1 / 13.1 / 17.1) in 7 phase-commits A-G: `a3f94f6` extend C FFI `aletheia_send_frame` 7→11 args (4 trailing u8 for present/value pairs) + Haskell `mkMaybeBool` helper + Agda `TimedFrame.brs/esi` docstring; `a4353f0` Python `CANFrameTuple.brs/esi` + `send_frame(brs=, esi=)` kwargs + `encode_maybe_bool` + `can_log._convert_message` lifts python-can `bitrate_switch`/`error_state_indicator` on `is_fd` frames; `cc04331` Go `Frame.BRS/ESI` + `Client.SendFrame(... brs, esi *bool)` (~25 callers updated mechanically; cgo trampoline + `Backend.SendFrameBinary` interface extended); `112c075` C++ `Frame.brs/esi` (`std::optional<bool>`) + `AletheiaClient::send_frame` default-`std::nullopt` kwargs + `IBackend::send_frame_binary` interface extended; `a8ade07` JSON `sendFrame` command added to Agda dispatch (StreamCommand `SendFrame` ctor + Routing `trySendFrame` + Handlers `handleSendFrame` delegating to proven `handleDataFrame`); `480e338` FEATURE_MATRIX row `canfd_brs_esi_fields` + PROTOCOL.md § 7 SendFrame full request/response shape + binary C signature updated to 11-arg ABI.  Cross-binding parity tests: 9 combinations `brs/esi ∈ {None, True, False}` round-tripping through real `libaletheia-ffi.so` in Python/Go/C++.  Bench: Stream LTL +21-26% (cumulative R19 win, not cluster-18 specific); Signal Extraction / Frame Building all within ±10% WSL2 gate (largest delta Python Frame Building -7.8% from 4 added `c_uint8` args' ctypes marshalling cost).  The Aletheia kernel does NOT consume BRS/ESI — pass-through metadata per ISO 11898-1:2015 §10.4.2 / §10.4.3; LTL atomic-predicate scope remains signal-level.  **Cluster 14** ✅ CLOSED 2026-05-12 — combinator-first refactors fully resolved: AGDA-C-6.3 `checkUnknownNodeReference` helper `3e744b6`, GO-A-6.3 `parseObjects[T]` generic + GO-A-6.2 stringer `6a0f687`+`a69ab11` (initial design-held adjudication reopened by user request for empirical verification; codegen-clean ship), AGDA-C-6.4 + 6.6 adjudicated design-held with empirical evidence `ea06421`+`4311699`+`9be35dc` (parameterised forms cost more machinery than the LOC saved; same cascade-of-machinery pattern as 6.1 InContext lift).  **Cluster 17** ✅ CLOSED 2026-05-12 (Python domain model coherence, all 22 sub-items shipped) — earlier-session 10 commits (`af6c592` mechanical sub-batch / `672e189` docstring sub-batch / `8dba04c` type-coherence batch / `10bb81b` test hygiene / `d7f8a06`+`8047074`+`dcf1178` bite-the-bullet reopen chain / `dcb2fbe` protocols.py split / `843c9e0` CAN-FD regression / `4197f85` pylint claim tightening) + this-session 7-commit closure: `3b2df3d` PY-D-20.4 `validation.py` → `issue_codes.py` rename (4 import updates + mutmut paths + 2 doc files), `2169ec3` PY-D-20.6 `@dataclass(frozen=True, slots=True) CheckRunResult`, `017ca5a` PY-D-20.3 `run_checks` lifted from cli.py to new `aletheia/checks_runner.py` (`_die`-exit-code → typed `AletheiaError` raises; layering inversion fix), `5b8791a` PY-D-20.1 kind-tagged `AletheiaError` hierarchy (added `FFIError` + `StateError` mirroring Go `ErrFFI`/`ErrState` and C++ `ErrorKind::Ffi`/`State`; removed overloaded `ProcessError`; 17 raise sites migrated by category; 6 test files updated; one test re-stated to expect `ProtocolError` from kernel handler_no_dbc lift), `e190b84` PY-D-19.1 Python predicate values `float` → `Fraction` per DecRat universal principle (8 TypedDicts migrated; `_RationalInput = int | float | Fraction` coercion at builder; `_coerce_to_float` for display), `1e4becc` GO-D-19.1 mirror of 19.1 (Go predicate fields `PhysicalValue`/`Delta`/`Tolerance` → `Rational`; `IntRational` + `RationalFromFloat` 10⁹-scaling helpers; `serializePredicate` 8 sites switched `float64()` → `serializeRational`; `validateRational` non-positive denominator + `rationalLess` cross-product min/max ordering; ~150 Go test sites two-pass perl regex), `132035d` cleanup of dead `Delta`/`Tolerance` `float64` aliases now-orphan after 1e4becc.  Cross-binding wire symmetry: predicate values now exact rational end-to-end (Python `Fraction` / Go `Rational` / C++ `Rational`); error hierarchy now kind-tagged across all 3 bindings.  Per-cluster commit hashes + scope live in `memory/project_review_round19.md`.

**R19 carry-over phase** ✅ CLOSED 2026-05-09 — 9 of 9 R18 carry-overs shipped (clusters A-G); R19-CARRY-1 partial (Bool fast-path final RE-DEFER per `feedback_with_in_eq_outer_abstraction_barrier.md`); other 8 closed. Detail: `memory/project_review_round19.md`.

**Cluster 8 + Phase 2b** ✅ closed 2026-05-11 — defense-in-depth bound checks at parser surfaces (kernel + bindings + handler + formatter proofs, 8 sub-phases) + typed `ParseErr (InputBoundExceeded BoundKind observed limit)` lifted to all 3 bindings for NestingDepth + AtomCount. Phase 2c (IdentifierLength) initially deferred pending parser-monad rewrite; later shipped 2026-05-13 in R20 cluster I via a different approach — `validateIdent` body split (decidability check first, then length on the `no` branch) + JSONParser return-type cascade `ParseError ⊎` → `Error ⊎`, no parser-monad change. Lessons: `feedback_handler_vs_parser_bound_placement.md`, `feedback_parsedbc_quadratic_scaling.md`. Detail: `memory/project_review_round19.md`.

**Memory-bound build infra** shipped 2026-05-11 via `43fcd4b` — `cabal build -j16 --ghc-options="+RTS -A64M -M3G -RTS"` (was unbounded `-j`). Lesson: `feedback_parallel_memory_budget.md`.

**R18 review round** ✅ CLOSED 2026-05-09 — 17 hard clusters + end-of-round basedpyright `benchmarks/` promotion; merged to `main` via `4518fef` (`--no-ff`); 112 hard findings cumulative. Local `main` 59 commits ahead of `origin/main`; not pushed (never push without explicit user direction). Detail: `memory/project_review_round18.md`.

**Standard gates passed at every closure** — `cabal run shake -- {build, check-properties, check-invariants, check-no-properties-in-runtime, check-erasure, check-fidelity, check-ffi-exports, count-modules, check-runbook, check-stability-bench}` + Python `pytest tests/` + Go `go test ./aletheia/ -count=1 -race` + C++ `ctest --test-dir cpp/build` + lint gates (basedpyright / pylint 10/10 / gofmt + go vet / clang-format + clang-tidy). Per-closure gate logs live in PROJECT_STATUS.md.

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
