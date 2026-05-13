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

248 total modules (`cabal run shake -- count-modules`):
- **243**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer — co-located here to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

247 of 248 modules use `--safe`. No modules require `--sized-types`. Per-commit module-count drift (Path A.4 cluster lift, Track E sub-phase additions, R18 cluster 14 extraction, R18 cluster 2 `Aletheia.Limits` extraction, R19 Phase 2 cluster 8 `Aletheia.DBC.Formatter.Bounded` extraction, R20 cluster V `Aletheia.DBC.BoundWalks` extraction, etc.) is recorded in PROJECT_STATUS.md and `memory/project_b3d_universal_proof.md` / `memory/project_track_e_val_promotion.md` / `memory/project_review_round18.md`.

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

**Active branch (2026-05-14): `review-r20`** — R20 review round in DEFER-end-of-round phase. Forked from `main` at `2e79ed8` 2026-05-12 (post R19 merge `41f6ba6` + post-merge tidy `2e79ed8` removing R18/R19 findings files; pushed to remote). Live commit count via `git rev-list --count main..HEAD` per `feedback_self_referential_count_drift.md` (formula only — literal omitted per the memory). Module count **248** (R20 cluster H added 3 `Aletheia.Limits` bound constants; cluster I extended JSONParser/Routing/Handlers/MetadataRoundtrip cascade `ParseError ⊎` → `Error ⊎` + added `tools/check_bound_enforcement.py`; cluster K added C++ `AletheiaException` class to `cpp/include/aletheia/error.hpp`; cluster N added `cpp/src/detail/loader_utils.{hpp,cpp}` + `go/excel/hardening.go`; cluster R is doc-only; cluster S is proof-only — two new lemmas in existing `Coalgebra/Properties.agda`, no module count change; cluster V extracted `Aletheia.DBC.BoundWalks` — 247 → 248). Python module count from R19 cluster 17 carries forward (+2 from protocols.py split + cli.py layering inversion).

**R20 review round** (started 2026-05-12) — 17 review agents → **671 raw findings** (`3571702`); cluster split (`3fa8e65`) into Clusters A-V + DEFER-end-of-round. **Clusters A-V ✅ CLOSED** + regen safety fix + N follow-up + P follow-up + S follow-up. Per-cluster commit hashes + full scope: `memory/project_review_round20.md`. Cluster summary (closure commits): A `4be9a84` conftest unblock; B `dbd3e60` Go nocgo stub; C `c2c6bab` cross-binding rational discipline; D `9a73a48` C++ batch bound_info forward; E `c795141` docs hygiene; F `036a684` BRS/ESI mock fidelity; G `00dc764` CHANGELOG R19 BREAKING; H `ea62e60` cardinality bounds + GO parseRational; I `33d0e44` BoundKind enforcement audit + FFI snapshot constructor coverage (+ safety fix `ba1f005`); J `efa041f` Python `ValidationError` migration (~58 sites, 13 modules); K `ee76e91` C++ `ErrorKind::Ffi` emission + `AletheiaException`; L `eb597f9` BRS/ESI doc-fence sweep; M `11f4100` logger fast-path guards (Go + C++) — new `Logger::enabled(LogLevel)` predicate + 6+6 hot-path Debug call-site guards mirroring Python R19 cluster 19 / PY-B-14.1; N `d5f28b8` Excel / YAML loader I/O hardening + Go follow-up `f39de48`; **O `8bb0055` Go DBC rename completion + wrap helper Error suffix — closes the R19 cluster 5 follow-up flagged in its CHANGELOG entry. Public-API: `NewDbcMessage`/`NewDbcDefinition` → `NewDBCMessage`/`NewDBCDefinition`, `Backend.FormatDbcBinary` interface + 4 implementations → `FormatDBCBinary`, `excel.WithDbcSheet` → `excel.WithDBCSheet`, `DBCRawValueDesc.CANID CANID` → `ID CANID` stutter fix. Unexported sweep across `parseDbc*` / `formatDbcFn` / `xlsxDbcSignal` / `parseDbcRows` / `extractDbcObject` / `makeDbcWorkbook` + ~15 `Test*Dbc*` test names. GO-A-3.4 wrap-helper symmetry: private `wrapValidation`/`wrapProtocol` → `wrapValidationError`/`wrapProtocolError`. GO-A-3.5/3.6/3.7 deferred with rationale (cross-binding fix needed for 3.5; structural typedef-vs-struct for 3.6; different sync mechanisms for 3.7). 18 files / +184 / -157**.  Follow-up `78dcda5` made the dispositions durable in `review-r20-findings.md`: GO-A-3.5 → `[DEFER]` + explicit DEFER-end-of-round entry, GO-A-3.6/3.7 → `[DROP]` (new lesson `feedback_findings_doc_disposition_sync.md` — commit-body rationale invisible to next planner scan if findings-doc marker stays `[ ]`). WSL2 jitter measured empirically 2026-05-12: median 1.70%, max 4.58% inter-batch CV; ±10% reference retained for session-distant comparisons (`feedback_wsl2_variance_stance.md`). **Cluster P** `4dd3c05` — Python `Backend` Protocol + `FFIBackend` + `MockBackend` shipped in new `python/aletheia/client/_backend.py` (~640 LOC); `AletheiaClient.__init__(backend=…)` DI seam; `gated_backend` replaces `gate_send_frame` setattr monkey-patch in `asyncio/testing.py`; `BinaryFFI` class removed from `_client_bin.py` (logic in `FFIBackend`); state handle type `int` (was `ctypes.c_void_p`); hot-path bound-method cache on `__enter__`. Closes R19 cluster 9 carry-over PY-D-24.1 + 24.2 + 24.3 + PY-B-22.2 + PY-B-12.2 + PY-B-25.2. FEATURE_MATRIX: NEW `backend_di_seam` row + Python `mock_backend` flipped to implemented. CHANGELOG: Added + BREAKING entries. NEW `tests/test_backend_protocol.py` (18 tests). Test-coverage follow-up `ac202e6`: post-commit advisor caught one test exercising the no-DBC-lookup JSON path instead of the BinaryPathUnsupportedError fallback its name claimed (canned parseDBC had `messages=[]`); fix populates lookup so the binary attempt fires. **Cluster Q** `e15bd6d` — Multi-binding Cat 1/4 hygiene sweep (35 files / +254 / -168 / no runtime semantics change). AGDA: `Aletheia.Main` facade extended with 5 drifted Protocol.Message ctors (SendFrame / ParseDBCText / FormatDBCText / DBCTextResponse / ParsedDBCResponse — AGDA-A-1.1); LookupStrategy / digitToNat / resultToString / TimeUnit / stale historical narrative comments rewritten (AGDA-A-1.2/1.4/1.8/1.9/1.10/4.1-4.7). GO: enrich.go / yaml.go / SignalByName / signalNameByIndex / isSigned / lockWaiters / CodeFrameInjectionFailed / SIG_GROUP_ comments cleaned (GO-A-1.3-1.5, 4.1-4.7, 4.9); SignalByName "deep copy" doc fixed (shallow). C++: `<cassert>` removed from types.hpp (CPP-A-1.3, no `assert()` macros); limits.hpp docstring reframed to cross-binding-mirror role (CPP-A-1.1/1.2); FfiBackend lifecycle invariant promoted to class docstring (CPP-A-4.3); AletheiaClient ctor gains doxygen (CPP-A-4.4). PYTHON: cli.py docstring lists all 6 subcommands (PY-A-4.1/33.1 — was missing `format-dbc`); DBCSignalMultiplexed docstring corrected (PY-A-4.2); `_ACK_BYTES`/`_ACK_BYTES_SPACED` inlined into `_ACK_RESPONSES` (PY-A-4.4); dsl.py three-point coupling pointer corrected (PY-A-4.5). INFRA: `.gitignore` typo fix `go/benchmarks/benchmark` → `benchmarks`; **cluster L flagged follow-up at `tools/run_ci.py:429` closed** — doc-harness extended to cover `python/README.md` + `examples/README.md` with explicit `--rootdir=<repo>` (pytest auto-detection picked up `python/pyproject.toml` as rootdir when `python/README.md` joined arg list); doc-fence count 114 → 116; TUTORIAL.md FP-verified. **Gate-surfaced regressions fixed** per `feedback_fix_tool_gate_violations.md`: basedpyright 12 errors on `_backend.py` Backend Protocol stubs (docstring-only `-> bytes` returns None) fixed with `raise NotImplementedError` body (both basedpyright NoReturn-happy and pylint real-body-happy — `...` triggered pylint's `unnecessary-ellipsis`; **cluster P shipped with this regression masked** — P session-state claim "basedpyright 0/0/0" was inaccurate); clang-tidy misc-include-cleaner errors in `mock_backend.hpp` for `std::span`/`std::byte`/`std::optional`/`std::move` (introduced by cluster F BRS/ESI signature at `036a684`) fixed by adding `<cstddef>`/`<optional>`/`<span>`/`<utility>`. FP-VERIFIED: AGDA-A-4.5, 1.5/1.6/1.7/1.11, GO-A-4.4/4.8, CPP-A-1.1/1.2, DOC TUTORIAL.md inclusion. DROPPED: GO-A-4.10 (CI value-parity tooling task). DEFER-end-of-round: AGDA-A-1.3 (helper-module extraction for `signalsBound` + `firstDBCOverBound`; cascades across two consumers' import graphs). CHANGELOG: Other entry for Agda facade extension. **Follow-up flagged for cluster R or after**: `vehicle_checks.xlsx` will recreate on every doc-harness run from `create_template` fences in COOKBOOK.md:506 + INTERFACES.md:467 (pre-commit `rm` kept the tree clean for cluster Q but the recurrence is real — conftest fix or `--rootdir=tmp_path` plumbing needed). **Cluster R** `10a07d6` — Go `Backend` interface gains structured grouping comments at `go/aletheia/backend.go` mirroring C++ `IBackend`'s [MANDATORY] / [OPTIONAL] split (3 groups: lifecycle + JSON command bus / binary-FFI send-event-state-transition endpoints / binary-FFI bidirectional endpoints).  Doc-only — method signatures unchanged.  Splitting into `CommandBackend` + `BinaryBackend` was considered and rejected because every `c.backend.*` consumer in `client.go` uses the full surface.  **GO-D-19.1 [FP]** with cross-binding evidence: all three bindings render predicate values through the same `to_double + g-format` pattern (Python `_coerce_to_float`, C++ `format_value(Rational)` → `r.to_double()` → `{:g}`, Go `Float64()` → `%g`); Go is consistent, not divergent; "wire form" is misleading (JSON wire is `{numerator, denominator}` not `N/D`); switching to literal `N/D` would render `Rational{23, 2}` (= 11.5, typical voltage threshold) as `"23/2"` — readability regression across the existing test corpus in all three bindings.  Smart-fallback renderer (exact decimal when DecRat-terminating, `N/D` otherwise) noted as Phase-6 alternative requiring user direction.  **New lesson distilled**: `feedback_cross_binding_consistency_as_fp.md` — when a per-binding finding's reviewer framing assumes the flagged binding is the outlier, a cross-binding grep can FP-verify the finding instead of widening the gap (two-question pre-disposition gate; conjugate to `feedback_cross_language_parity.md`).  Disposition drift cleanup per `feedback_findings_doc_disposition_sync.md`: GO-D-15.1 + GO-D-15.2 (closed by cluster O `8bb0055` but markers left `[ ]`) flipped to `[FIX]`; GO-D-22.2 (body documents "clean") flipped to `[FP]`.  DEFER-end-of-round expanded with `vehicle_checks.xlsx` doc-harness recreation flagged from cluster Q (two candidate fix shapes documented: conftest cwd redirect or `tmp_path` inject).  CHANGELOG Other entry for the Backend interface docstring grouping.  **Cluster S** `637b2e0` — **AGDA-B-26.x DEFER block + AGDA-B-9.2 partial closure**.  Disposition flips: 26.1 `[FP]` (parse-time validator Dec cold-path), 26.2 `[FP]` (`lookupByKey` cold-path with in-source revisit-signal comment), 26.3 `[DEFER]` (`injectHelper` Bool fast-path R19-CARRY-1 RE-DEFER per `feedback_with_in_eq_outer_abstraction_barrier.md` four-approach probe — direct rewrite / `mkBoundedBitVec` / `@0`-with-Bool / `.()`-irrelevance), 18.3 `[DEFER]` (same scope; original "26.5" typo corrected to 26.3), GA9.1 `[DEFER]` (same where-block scope).  **AGDA-B-9.2 [FIX-PARTIAL]**: discovery surfaced the `Internals.agda:225-238` "stability argument" comment as factually wrong on two counts — (1) `Always` proc never returns Satisfied (`combineAnd` RHS is `Continue`, output is `Continue`/`Violated` only, never `Satisfied` — contra the original comment claim); (2) re-stepping after Satisfied does NOT always return Satisfied/Continue; concrete witness via direct definitional unfolding of `LTL/Coalgebra.agda`: `Until (Atomic 0) (Atomic 1)` with table 1 True at y₁ reduces to `combineOr Satisfied _ = Satisfied`; same proc at y₂ with both atoms False reduces to `combineOr (Violated _) (Violated _) = Violated _` (third pattern matches `combineOr (Violated _) r = r`, r = Violated).  Cluster S delivers: (i) **Comment rewrite** at `Internals.agda:225-238` accurately describing safe shapes (Always-wrapped: Satisfied unreachable; Eventually-wrapped: re-stepping safe) vs latent (top-level Until/Release/MetricUntil/MetricRelease/raw Atomic/And/Or-of-atomic).  (ii) Two **provable** step-level lemmas in `Coalgebra/Properties.agda` — `stepL-always-never-satisfied` (Satisfied branch unreachable for the canonical CAN safety pattern) and `stepL-eventually-never-violated` (re-stepping safe for Eventually-shaped proc); existing "VERDICT STABILITY" comment block also updated to clarify those describe trace-level `runL` convergence not step-level proc reuse.  (iii) New project memory `project_classify_satisfied_soundness_gap.md` documenting the latent gap + two viable closures: (a) operational fix — drop the prop from the iteration list on Satisfied (runtime-behaviour change; extends `StepOutcome` with `complete` ctor; needs full gate suite + benchmark + monotonic-shrink theorem); (b) surface restriction — `parseProperty`-tier rejection of non-Always/non-Eventually top-level formulas (API break); both need user direction per `feedback_no_silent_proof_reframing.md` so cluster S delivers only the comment correctness + structural lemmas that are actually true.  A universal `stepL-satisfied-stable` quantifying over arbitrary `LTLProc` is NOT a theorem (latent gap is proof obstruction); `AGDA-B-9.2-residual` carried to DEFER-end-of-round.  Cluster S follow-up `d838fa5` dropped the misleading external memory-path reference from `Internals.agda:267`.  **Cluster T** `a1fe3fe` — DOC-A-1.14 + vehicle_checks.xlsx doc-harness recreation closed in one commit per `feedback_no_unilateral_deferral.md`.  AGENTS.md:751 future-tense paragraph rewritten as past-tense (three audit scripts + `.github/dependabot.yml` shipped 2026-05-09; R20 surfaced hardening findings on the scripts themselves — CICD-1.2/1.3/2.3/3.2/5.1; workflow actions still tag-pinned, SHA migration remains in cat 1 queue).  Repo-root `conftest.py` gained autouse `_sandbox_cwd` fixture pinning per-test cwd to `tmp_path` via `monkeypatch.chdir` — defense-in-depth on top of `pytest_sessionstart` patches; doc fences are cwd-independent (loader fakes ignore path args); doesn't defend the rootdir-mismatch case (operator-error path documented in AGENTS.md § Python Cat 32 Verification).  **Cluster U** `7fc7b0b` — Cat 27 stdlib coverage: `Parser/Combinators.agda` `elem` replaced with point-free `any (c ≈ᵇ_)` via stdlib `Data.Bool.ListAction.any` (AGDA-C-27.2); `DBC/JSONParser.agda` `_≟-LC_` renamed to `_≟ₗᶜ_` per the subscript convention (AGDA-C-27.3, 8 use sites).  Dispositions: AGDA-C-27.1 (`sameLengthᵇ`) `[DEFER]` (downstream structural lemmas pattern-match on definition; ~30+ proof cascades); AGDA-D-19.3 + GA20.1 (`nothing≢just`) `[FP]` (3-line local absurdity helper idiomatic).  Cluster U CHANGELOG bundled cluster T catch-up entries since T shipped without them.  **Cluster V** `6e8afc9` — AGDA-A-1.3 helper-module extraction: new sibling module `Aletheia.DBC.BoundWalks` (157 LOC, 18 functions) houses the cardinality `vds*` family + string-length `firstOverBound*` family previously duplicated between `Handlers.agda` and `Handlers/ParseDBCText.agda`.  Cycle-avoidance closed by leaf-level placement (imports only `DBC.Types` + `Limits`; no cycle).  Per-handler `signalsBound` / `firstDBCOverBound` / `firstStringOverBound` aggregators stay local because return types differ (named `Maybe (String × ℕ × ℕ)` vs unnamed `Maybe (ℕ × ℕ)`).  Module count **247 → 248**.  6 files / +206 / -223 (net -17 LOC).  Next: **DEFER-end-of-round pass remainder** (AGDA-B-9.2-residual operational-fix-vs-surface-restriction, C++ Strong<Tag,T> + LtlFormula portability, DEFERRALS.md updates, GO-A-3.5 cross-binding mux field naming, GO-D-19.1 smart-fallback renderer), then R20 ready for `--no-ff` merge to main per R18/R19 precedent. Gates fresh at every cluster ship: **11 Agda gates clean** (build + check-properties / check-invariants / check-no-properties-in-runtime / check-erasure / check-fidelity / check-ffi-exports / check-bound-enforcement / count-modules / check-runbook / check-changelog); pytest **850p+1s** (+3 from P follow-up `ac202e6` close in cluster Q); Go test -race (both `go/aletheia/` and `go/excel/`); C++ ctest 10/10; basedpyright 0/0/0; pylint 10.00/10 on `aletheia/ tests/ ../conftest.py`; gofmt + go vet + clang-format + clang-tidy clean; doc-fence harness 116/116.

**R19 Phase 2 ✅ MERGED to main** via `41f6ba6` (`--no-ff`) 2026-05-12; post-merge tidy `2e79ed8` removed R18/R19 findings files; pushed to remote. 17 review agents → 19 clusters; **19 of 19 closed**. Highlights: cluster 17 closed Python domain model coherence (22 sub-items; kind-tagged `AletheiaError` hierarchy with `FFIError`/`StateError` mirroring Go `ErrFFI`/`ErrState` and C++ `ErrorKind::Ffi`/`State`; predicate values `float` → `Fraction` per DecRat universal principle; Go mirror `IntRational` + `RationalFromFloat`); cluster 18 closed BRS/ESI cross-binding plumbing in 7 phase-commits A-G (C FFI `aletheia_send_frame` 7→11 args; Python/Go/C++ `Frame.brs/esi`; JSON `sendFrame` dispatch; FEATURE_MATRIX row `canfd_brs_esi_fields`; cross-binding parity tests 9 combinations); cluster 19 closed hot-path allocations (Python `_ACK_RESPONSES` hoist + `from_buffer_copy` + `isEnabledFor` guards; C++ `last_frames_` find-then-emplace; Go `serializeDataFrame` design-held). Per-cluster commit hashes + scope: `memory/project_review_round19.md`.

**R19 carry-over phase** ✅ CLOSED 2026-05-09 — 9 of 9 R18 carry-overs shipped; R19-CARRY-1 partial (Bool fast-path final RE-DEFER per `feedback_with_in_eq_outer_abstraction_barrier.md`). Detail: `memory/project_review_round19.md`.

**Cluster 8 + Phase 2b** ✅ closed 2026-05-11 — defense-in-depth bound checks at parser surfaces (kernel + bindings + handler + formatter proofs) + typed `ParseErr (InputBoundExceeded BoundKind observed limit)` lifted to all 3 bindings for NestingDepth + AtomCount. Phase 2c (IdentifierLength) shipped 2026-05-13 in R20 cluster I via handler-boundary approach, no parser-monad rewrite. Lessons: `feedback_handler_vs_parser_bound_placement.md`, `feedback_parsedbc_quadratic_scaling.md`.

**Memory-bound build infra** shipped 2026-05-11 via `43fcd4b` — `cabal build -j16 --ghc-options="+RTS -A64M -M3G -RTS"` (was unbounded `-j`). Lesson: `feedback_parallel_memory_budget.md`.

**R18 review round** ✅ CLOSED 2026-05-09 — 17 hard clusters + end-of-round basedpyright `benchmarks/` promotion; merged to `main` via `4518fef` (`--no-ff`); 112 hard findings cumulative. Detail: `memory/project_review_round18.md`.

**Standard gates passed at every closure** — `cabal run shake -- {build, check-properties, check-invariants, check-no-properties-in-runtime, check-erasure, check-fidelity, check-ffi-exports, check-bound-enforcement, count-modules, check-runbook, check-changelog}` + Python `pytest tests/` + Go `go test ./aletheia/ -count=1 -race` + C++ `ctest --test-dir cpp/build` + lint gates. Per-closure gate logs live in PROJECT_STATUS.md.

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
