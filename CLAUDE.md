# CLAUDE.md

Guidance for Claude Code (claude.ai/code) when working in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). Core logic in Agda with correctness proofs, compiled to Haskell, exposed through Python, C++, and Go APIs. Phase status: [PROJECT_STATUS.md](PROJECT_STATUS.md). Mission: [docs/PITCH.md](docs/PITCH.md).

## Development Environment

**Must be preserved across session compression.**

- Agda binary: `/home/nicolas/.cabal/bin/agda`
- Shell: `/usr/bin/fish` (config at `/home/nicolas/.config/fish/config.fish`)
- User binaries: `/home/nicolas/.local/bin`; libraries: `/home/nicolas/.local/lib`
- **Optional GHA toolchain** (for `tools/run_ci.py` step 18 + local `act` pairing — see [docs/development/CI_LOCAL.md](docs/development/CI_LOCAL.md)):
  - `actionlint` — workflow YAML lint. Install:
    ```bash
    ACTIONLINT_VERSION=1.7.7
    curl -fsSLO "https://github.com/rhysd/actionlint/releases/download/v${ACTIONLINT_VERSION}/actionlint_${ACTIONLINT_VERSION}_linux_amd64.tar.gz"
    sudo tar xzf "actionlint_${ACTIONLINT_VERSION}_linux_amd64.tar.gz" -C /usr/local/bin actionlint
    ```
  - `act` — local GHA replay. Install: `curl -fsSL https://raw.githubusercontent.com/nektos/act/master/install.sh | sudo bash`. Requires Docker.

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

246 total modules (`cabal run shake -- count-modules`):
- **241**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer — co-located here to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

245 of 246 modules use `--safe`. No modules require `--sized-types`. Per-commit module-count drift (Path A.4 cluster lift, Track E sub-phase additions, R18 cluster 14 extraction, R18 cluster 2 `Aletheia.Limits` extraction, etc.) is recorded in PROJECT_STATUS.md and `memory/project_b3d_universal_proof.md` / `memory/project_track_e_val_promotion.md` / `memory/project_review_round18.md`.

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

**Pre-commit minimum** (doc-only changes): `agda +RTS -N32 -RTS src/Aletheia/Main.agda` → `cabal run shake -- build` → relevant binding tests.

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

**Most recent activity (2026-05-08, on `review-r18` branch):** R18 review round in flight; Rounds 1 + Round 1 follow-up + Rounds 2-10 closed; **cluster 1 fully closed across 7 phased commits** (offline CI bootstrap + GHA meta-gates + dependabot + first-end-to-end orchestrator-defects fix per `memory/feedback_orchestrator_end_to_end_validation.md`).  Forty-five commits on `review-r18` (forked from `main` at `b4528ee`): `9ff434b` AGENTS.md +13 R18 protocol additions (3 universal rules — adversarial-input bounds, reproducible builds, CHANGELOG discipline; Agda cat 32 parser resource bounds; Go cat 33 / C++ cat 33 / Python cat 34 dynamic correctness; cat 14/27/26/25/28 sub-checks; new top-level CI/CD section); `df16e92` findings seed; `4420b03` Agda Agent B re-run integration (after first-pass stub; tightened scope ~15 priority modules / 30-50 cap returned 8 findings in 7min); `ae9fe67` Round 1 fixes (47 files +56/-96 — clusters 15 mechanical batch + 9 module count drift); `c536fb2` Round 1 dispositions recorded; `d640789` UPD; `a1648bd` Round 1 follow-up — cluster-15 over-prune of `signalNameStr` from `Aletheia.DBC.Types using` clause in `SignalExtraction.agda` (`ae9fe67`'s "all 8 gates clean" claim was incorrect: `.so` mtime predated the source edits, gates were captured against an earlier state; lesson saved as new `memory/feedback_gate_claim_integrity.md` and routed as a deferred sub-item under cluster 1); `a30d184` Round 2 — cluster 8 / UR-1.1 `CHANGELOG.md` bootstrap (Keep-a-Changelog 1.1.0 + SemVer 2.0.0; `[2.0.0] — Unreleased` seeded with v1.1.1 → HEAD public-API diff across Python / Go / C++; honest SemVer given the breaking signature refactor on every Go ctx-first / C++ stop_token-first Client method); `b6e6d91` cluster 1 (CICD bootstrap) scope expansion — three deferred sub-items now route there: (a) `tools/check_changelog.py` enforcement, (b) gate-claim-integrity gate with attached `tools/ci-output/<sha>.log` artifact, (c) Shake `phony "ci"` orchestrator + `act` Docker pairing + pre-push hook auto-install via `tools/install_hooks.py` (user-directed, motivated by limited GitHub Actions monthly allotment); `884f682` UPD recording the above; (next) Round 3 — cluster 10 (Go's 16th `dbc.text_parsed` log event) closed via 1-line surface rename in `go/aletheia/client.go:287` (`dbc.text_parsed` → `dbc.parsed`; per AGENTS.md cat 22 "Python is the reference") + missing-mechanism gate (`docs/LOG_EVENTS.yaml` 15-event SSOT + 3 per-binding parity tests `python/tests/test_log_events_parity.py` / `go/aletheia/log_events_test.go` / `cpp/tests/test_log_events_parity.cpp`, mirroring the FEATURE_MATRIX pattern from PARITY_PLAN Track A); gate-shape verified by temporary revert producing precise `emitted event "dbc.text_parsed" is not in docs/LOG_EVENTS.yaml` diagnostic.  Closes 6 findings (GO-A-30.1, GO-A-4.1, GO-S-22.1, PY-S-22.1, CPP-S-22.2, DOC-X-5.12).  17 review agents → ~610 findings → 17 clusters ranked FIX-early / FIX-middle / DEFER-end-of-round per `feedback_review_round_dispositions.md`.  Round-state in `memory/project_review_round18.md`.  Disposition rules captured in `memory/feedback_review_round_dispositions.md` (Rule 1: DEFER means end-of-round sequencing not rejection; Rule 2: FP needs explicit double-check — surface fixes can hide missing mechanisms; Rule 3: one document per round).  Round 4 — `3adcdec` cluster 13 closed: CANCELLATION.md L150 `AletheiaClient(dbc=, checks=load_checks())` was a hallucination (`git log -S "dbc=" -- python/aletheia/client/_client.py` returned no commits — never planned-then-dropped) → rewritten to `AletheiaClient(default_checks=load_checks("checks.yaml"))` plus `await client.parse_dbc_text(...)`; L302/L324 stale `AsyncAletheiaClient` → `aletheia.asyncio.AletheiaClient`; L324 stale matrix rows `lazy_frame_iter` / `cancellation` → `lazy_streaming_batch` / `cancellation_contract`; same kwargs fix at `python/aletheia/asyncio/__init__.py:15` rst docstring; missing-mechanism gate: `docs/architecture/CANCELLATION.md` joined the Python doc-example harness `DOC_FILES` (already in Go/C++ harness scopes); AGENTS.md § Python Cat 32 verification block + prose updated.  Limitation acknowledged: pytest-markdown-docs only executes top-level statements so a defined-but-not-invoked `async def` body is not body-checked at fence-execution time (Go and C++ harnesses wrap in synthesized `main()` and do execute).  Closes DOC-A-1.13/14/15 + PY-S-15.1.  Round 5 — `bbaf9a8` cluster 11 closed: `iter_can_log` 4-tuple unpack fixed at 7 doc sites (QUICKSTART:96 / TUTORIAL:258 / PITCH:190 / PYTHON_API:33 [comment] / 44 / 771 / 879) — `iter_can_log` yields `CANFrameTuple(timestamp_us, arbitration_id, dlc, data, extended)`; the docs were unpacking 4 fields against a 5-field NamedTuple; missing-mechanism gate: `conftest._harness_iter_can_log` flipped from `iter(())` to `iter([CANFrameTuple(0, 0x100, 8, bytes(8), False)])` so unpack arity is exercised at fence-execution time; gate-shape verified by forward-order revert producing 5 fences failing with the precise diagnostic `ValueError: too many values to unpack (expected 4)`.  Three iter_can_log fences without explicit `start_stream` (COOKBOOK:189/419 + PYTHON_API:879) pass even after the harness change because `send_frame` returns an `ErrorResponse` (not raises) when called outside stream mode — no stream-wrap additions needed.  Closes DOC-B-15.1-6.  Round 6 — `46308cd` cluster 12 closed: C++ JSON parser drops `unresolvedValueDescs` fixed by adding `parse_raw_value_desc` static helper to `cpp/src/json_parse.cpp` mirroring `raw_value_desc_to_json` in `cpp/src/json_serialize.cpp`; missing-mechanism gate: 3 regression tests in `cpp/tests/unit_tests_json.cpp` `[trackE]`-tagged (parse, serialize→parse roundtrip, missing-key tolerance); gate-shape verified by `git stash` of just `cpp/src/json_parse.cpp` → 2/3 tests fail with `unresolved_value_descriptions.size() 0 == 1` → restore → 3/3 pass (31 assertions); restores cross-binding parity (Python `_helpers.py:670` ✓, Go `json.go:1344` ✓, C++ ✓).  Closes CPP-B-11.3 + CPP-S-22.1.  All gates green at the cluster 12 ship commit: 8 Agda gates (build 1m45s / `count-modules` 244 unchanged; doc/test-config edits don't drift any proof so check-properties / check-invariants / etc. not re-run per "For doc-only edits, build alone suffices") + Python pytest 763p+1s (cumulative +1 from new `test_no_notest_python_fences[CANCELLATION.md]` parametrize case in Round 4) + markdown-docs harness 106 passed across all 12 user-facing doc files + Go test -race ok + C++ ctest 9/9 (`unit_tests` now runs 3 additional cases / 31 additional assertions in Round 6) + basedpyright 0/0/0 + pylint 10.00/10 + gofmt + go vet + clang-format + clang-tidy.  Two cluster-15 items deferred for user judgment (AGDA-A-2.1/2.2 magic 2048; AGDA-A-4.1 open-ended TODO).  Round 7 (2026-05-08) — `02b346f` cluster 14 closed via Option (i) pure rename + extraction (advisor-recommended after verifying the dead 1-field stub and the JSON-side `WellFormedDBC` ↔ `WellFormedDBCRT` weak/strong pair was an intentional pattern not to break): deleted dead 1-field `WellFormedTextDBC` stub from `Formatter/WellFormedText.agda` (companion records `WellFormedTextSignal` / `WellFormedTextMessage` / `WellFormedTextPresence` / `MasterCoherent` are alive and stay); renamed text-side 8-field record `WellFormedDBC` → `WellFormedTextDBCAgg` and moved type definition from `Aggregator/Universal.agda` to a new dedicated module `Aletheia.DBC.TextParser.WellFormed` (closes AGDA-D-GA20.4 type-def-vs-theorem split); JSON-side `WellFormedDBC` UNCHANGED.  AGDA-D-11.2 closed by documenting the JSON-vs-text WF asymmetry as deliberate in both module headers (text emission is materially lossier — `Vector__XXX` placeholders / dropped `BO_TX_BU_` / multi-value mux / orphan `unresolvedValueDescs` — so predicates must differ; no invariant gap).  AGDA-D-19.6 closed per G-A7(c) "documented caller obligation": `Aletheia/Protocol/Handlers/FormatDBCText.agda` now explicitly documents the round-trip contract — handler emits text unconditionally (formatter is total), but `parseText (formatText d) ≡ inj₂ d` only applies when input DBC satisfies `WellFormedTextDBCAgg`; discharge happens at the input-source boundary (DBCs from `parseDBCText` carry the witness by construction; DBCs from `parseDBC` + clean `validateDBC` discharge `msg-ids-unique` (CHECK 18) and `unresolved-empty` (CHECK 23); other fields auto-discharge from refinement-types `Identifier` invariant; hand-constructed JSON DBCs are caller-responsibility); a stricter runtime-check variant (decidable `WellFormedTextDBCAgg?` + handler reject + new typed error) was estimated at ~300-500 LOC and not pursued.  Module count 244 → 245 (+1 for the new `TextParser.WellFormed` module).  Files touched: 2 new + 9 modified; 19 references renamed in `Aggregator/Universal.agda` + 1 load-bearing import + 1 type-signature in `Substrate/Unsafe.agda` + 5 comment refs (`TextParser.agda` / `Validator/Checks.agda` / `Types.agda` / `Formatter/WellFormedText/ValueDescResolves.agda` / `FormatDBCText.agda`).  Closes 5 findings (AGDA-D-11.1 / 11.2 / 15.4 / 19.6 / GA20.4).  All gates green: build 2m06s, check-properties verified, check-invariants / check-no-properties-in-runtime / check-erasure / check-fidelity / check-ffi-exports / count-modules 245 (verified via fresh `.so` mtime 05:53 newer than every source edit 05:40-05:51), Python pytest 763p+1s + markdown-docs harness 106 passed against fresh `.so`, Go test -race ok 3.747s, C++ ctest 9/9, basedpyright 0/0/0, pylint 10.00/10, gofmt + go vet + clang-format + clang-tidy clean.  Round 8 (2026-05-08) — cluster 16 closed via single bundled commit refactoring 4 of 5 AGDA-B-8.* findings: Step.agda 8.1/8.2 (real G-A2 violations on Response-shaped record goals — 3-rewrite chains became one `rewrite mono` for the case-dispatch on `with checkMonotonic prev tf` + a single `cong (λ p → proj₂ (dispatchIterResult dbc p tf updatedCache)) iter-eq` where `iter-eq` is built from `trans (iterate-correct step props) (cong (specResult step props ,_) spec-eq)`); Bounded.agda 8.3/8.4 (NOT G-A2 violations per advisor — small ℕ- and `++ₗ`-shaped goals fall in G-A2's small-goal carve-out — but cat 6 redundant-pattern findings; extracted private `binary-counter-step` and `binary-acc-spec-step` helpers consuming both IHs once each, the 12 binary clauses across `indexHelper-counter` and `collectAtomsAcc-spec` collapse to one-line dispatchers); Cache.agda 8.5 SKIPPED per advisor as small-goal non-violation (2 rewrites do essential variable rewriting via `≡csᵇ-sound` + `≡csᵇ-refl-eq`, refactor would cost ~5 lines for no real win).  **Benchmark prose correction**: prior session-state and `project_review_round18.md` claimed "benchmark required per cat 16 hot-path rule because Step.agda is in Main's runtime closure"; verified by grep that `Aletheia/Main.agda` and `Aletheia/Main/{JSON,Binary}.agda` import zero `FrameProcessor.Properties.*` modules (only one comment-block reference to `StreamingWarm.streaming-warms-cache`); cat 16's "transitively imported into Main.agda" trigger does not fire on Properties files; cluster 16 is proof-only and binding-test/benchmark-load-bearing-free.  Module count stays at 245 (helpers added inside existing `private` block).  Files touched: 3 modified — `Bounded.agda` (helpers + 12 clause collapses), `Step.agda` (2 lemmas + `specResult` import + `trans`/`cong` imports), `review-r18-findings.md` (dispositions).  All gates green: build 1m53s, check-properties 8m03s "All proof modules type-checked successfully!", check-invariants ✓, check-no-properties-in-runtime ✓, check-erasure 1m44s, check-fidelity ✓ 1/1, check-ffi-exports 11 entries, count-modules 245.  Sanity-check binding tests (no runtime impact expected, ran for gate-claim integrity per `feedback_gate_claim_integrity.md`): Python pytest 763p+1s, Go test -race ok 3.232s, C++ ctest 9/9 100% (24.65s).  `.so` mtime 06:54 newer than every source edit (06:49-06:51) verified via `stat -c '%Y %n'`.  **8 DEFER-end clusters open** (1, 2, 3, 4, 5, 6, 7, 17).  Round 9 (2026-05-08) — `7f64605` user-judgment items closed: AGDA-A-2.1 / 2.2 (magic `2048` in `Properties/Comments/Comment.agda`) via cascade fix per advisor — lemma `2048<extFlagBit` → `standard-max<extFlagBit` (body uses `standard-can-id-max` constant), sole call site at `buildCANId-rawCanIdℕ` (L156) updated, prose comment block at L125-133 swept consistently (`2048` → `standard-can-id-max`, `2^31` → `extFlagBit`, `2^29` → `extended-can-id-max`); AGDA-A-4.1 (`digitChar-not-isHSpace` open-ended TODO in `Format/ValueDescription.agda`) via scope-in consolidation per advisor's import-graph check (verified `Properties.Attributes.Assign.Common` upstream of every Format/* and Properties/CharClassDisjoint, no cycles either direction) — 5 private duplicates (Format/EnvVar, Format/ValueDescription, Format/ValueTable, Format/Comments, Properties/CharClassDisjoint) replaced with `open import ... Common using (digitChar-not-isHSpace)`, canonical at `Common.agda:56` already exported and consumed by Network/Topology.Message/SignalLine.Roundtrip; TODO comment removed; AGDA-B-8.5 user-judgment closure is no-op accept of advisor's SKIP recommendation (small-goal carve-out applies, refactor would cost ~5 lines for no win on a non-violation, disposition was already `[x] SKIPPED Round 8` in findings.md L166).  Module count: 245 unchanged.  Files touched: 6 modified Agda (`Comment.agda` cascade + 5 consolidation sites) + `review-r18-findings.md` dispositions.  All gates green: build via `agda Main.agda` against full runtime closure (Format/{EnvVar,ValueDescription,ValueTable,Comments} all checked successfully), check-properties 10m17s "All proof modules type-checked successfully!", check-invariants ✓, check-no-properties-in-runtime ✓, check-erasure 1m43s, check-fidelity ✓ 1/1 (1m49s), check-ffi-exports 11 entries, count-modules 245.  Sanity-check binding tests (proof-only edits, not load-bearing): Python pytest 763p+1s, Go test -race ok 3.115s, C++ ctest 9/9.  Cumulative across Rounds 1-9: **36 findings closed** (Round 9 ship contributed 3 — AGDA-A-2.1 / AGDA-A-2.2 / AGDA-A-4.1; AGDA-B-8.5 stays SKIPPED-not-closed per advisor + small-goal carve-out).  **Cluster 1 phases 1-3 closed 2026-05-08** (offline CI bootstrap, zero GitHub Actions allotment cost): `96fdcfd` phase 1 `tools/check_changelog.py` (UR-1 enforcement, branch-level granularity, gate-shape verified by forward-revert in detached worktree); `e7bf797` phase 2 `tools/check_gate_claim.py` (mechanical enforcer for `feedback_gate_claim_integrity.md` via `build/libaletheia-ffi.so` mtime invariant, three modes: pre-commit / HEAD / commit-hash audit); `30dd178` phase 3 `tools/run_ci.py` 17-step orchestrator + `tools/install_hooks.py` idempotent pre-push hook installer (8 Agda gates + 2 offline enforcers + 3 binding tests + 4 lints, ~12-15 min warm, log capture under `tools/ci-output/ci-<branch>-<timestamp>.log`).  Direct-invocation pattern (NOT through Shake `phony "ci"`) discovered empirically — initial Shake-target design exited at step 1 in 0s due to cabal-install flock recursion (parent `cabal run shake -- ci` holds `dist-newstyle/` flock, inner `cabal run shake -- build` fails to acquire it).  Limitation documented in Shakefile.hs comment block; pre-push hook calls `tools/run_ci.py` directly to avoid the recursion.  Phases 4-6 closed 2026-05-08 (same session) per user direction — Docker OK as dev dep, push-only `.github/workflows/` (correctness via pre-push hook), weekly dependabot: `2156d7c` phase 4 `.actrc` + `docs/development/CI_LOCAL.md` (act Docker pairing config + 3-layer architecture doc covering offline correctness sweep / push-time meta-gates / local GHA replay); `27e3ae3` phase 5 `.github/workflows/gha-checks.yml` minimal push-only meta-gate workflow (single `actionlint` job, installed via direct release tarball v1.7.7, no third-party action dependency for SHA-pin bootstrap); `8f656f5` phase 6 closes CICD-1.1-1.5 fully — `tools/check_action_pins.py` (github-owned tag-OK / third-party SHA-required / branch-refs rejected, gate-shape verified by synthetic violation worktree), `tools/check_workflow_permissions.py` (yaml-aware via python3+pyyaml, rejects read-all/write-all defaults), `.github/dependabot.yml` (weekly cadence covering pip in `python/`, gomod in `go/` and `go/excel/` separately, github-actions in root; Cabal not covered — no dependabot ecosystem support for Hackage), workflow expanded from 1 to 3 jobs (actionlint + action-pins + permissions-check), `tools/run_ci.py` extended from 17 to 20 steps (added GHA meta-checks 18-20 with skip-if-actionlint-not-installed), CLAUDE.md § Development Environment + actionlint + act install commands documented.  **Phase 7** (`66dd6f9` 2026-05-08) — first-end-to-end orchestrator-defects fix: phase 6 ship claimed "cluster 1 fully closed" without ever running `tools/run_ci.py` end-to-end; first end-to-end found 4 defects (steps 13/16/17 silently no-op'ing from `run_step_in` `$*` quote-drop on inner `bash -c "..."`; step 15 exit-code-vs-score mismatch against AGENTS.md L611 score-based pylint policy; step 16 `gofmt -d` always-exits-0 instead of `gofmt -l` per AGENTS.md L190; step 18 clang-tidy missing entirely per AGENTS.md L494 + `feedback_clang_tidy_mandatory.md`).  Phase 7 fixes all four; total steps 20→21; first genuine end-to-end pass `tools/ci-output/ci-review-r18_-2026-05-08T*.log` (18m38s wall, ALL 21 STEPS PASSED).  Forward-revert gate-shape verified for steps 15 / 16 / 17 / 18 (inject pylint score-drop / gofmt extra-space / clang-format bad-indent / clang-tidy missing-include → step fails with precise diagnostic; restore → step passes).  New `memory/feedback_orchestrator_end_to_end_validation.md` generalizes `feedback_gate_claim_integrity.md` from individual gates to chains of gates.  One sub-finding deferred: `tests/yaml_tests.cpp:262` `CHECK_THAT` misc-include-cleaner — out of phase 7 step 18's canonical AGENTS.md L580 src/*.cpp scope, tracked in `review-r18-findings.md` Cluster 1 deferred section for next-time-tests-tighten.  **Cluster 1 fully closed.**

**Cluster 2 closed 2026-05-08** (single bundled commit per Plan A + advisor — UR-2 adversarial-input bounds): NEW Agda module `Aletheia.Limits` (245 → 246 modules) hosting `BoundKind` enum (7 wire codes) + 11 numeric bound constants (max-dbc-text-bytes / max-json-bytes = 64 MiB; max-nesting-depth = 64; max-messages-per-file = 10K; max-signals-per-message = 1024; max-attributes-per-file = 10K; max-value-descriptions-per-file = 1M; max-identifier-length = 128; max-string-length-bytes = 64 KiB; max-atom-count-per-property = 1024; max-frame-byte-count = 64) + `withinBound` Bool fast-path helper.  `InputBoundExceeded : BoundKind → ℕ → ℕ → <ADT>` constructor added to `ParseError` / `DBCTextParseError` / `FrameError` (3 of 7 ADTs per advisor scope reduction — `RouteError` / `HandlerError` lift via existing `WrappedParse`; `ExtractionError` / `DispatchError` are downstream of parser entry); 7 new wire codes mirrored across all 3 bindings (parse_input_bound_exceeded / dbc_text_input_bound_exceeded / frame_input_bound_exceeded plus parse_invalid_identifier / dbc_text_parse_failure / dbc_text_trailing_input / dbc_text_attribute_refinement_failed which were pre-existing parity drifts in C++/Go).  Two Agda parser FFI entries capped: `Main.JSON.processJSONLine` (input-length cap on `parseJSON` before invoking it) and `Protocol.Handlers.ParseDBCText.handleParseDBCText` (input-length cap on `parseText`); both use the existing `wrapJSON` error-response path.  Per advisor (2026-05-08): `attachValueDescs` and `mkPredTable` NOT bounded directly — they consume already-parsed input; capping their producers (parseJSON / parseDBCText input cap) bounds them transitively without signature cascade.  `docs/architecture/PROTOCOL.md § Limits` documents the 11 bounds + 3 wire codes + dual-layer (Agda kernel + per-binding FFI entry) enforcement.  Per-binding mirrors: Python `aletheia.limits` module + `aletheia.InputBoundExceededError` exception class (subclass of `AletheiaError` with `kind`/`observed`/`limit` fields, raised by `_send_command` / `dbc_to_json` / `yaml_loader._load_yaml`); Go `aletheia/limits.go` + `*aletheia.InputBoundExceededError` typed error (errors.As-discoverable, returned by `FFIBackend.Process`); C++ `<aletheia/limits.hpp>` + `aletheia::InputBoundExceededError` value-type struct (re-exported from umbrella `<aletheia/aletheia.hpp>`; `FfiBackend::process` synthesizes `parse_input_bound_exceeded` JSON error response on oversize input).  Python `error_codes.py` enum extended with 6 new codes (PARSE_INPUT_BOUND_EXCEEDED, DBC_TEXT_*, FRAME_INPUT_BOUND_EXCEEDED); `test_error_code_sync.py`'s `_ERROR_CODE_FUNCTIONS` extended to include `dbcTextParseErrorCode` (was a pre-existing parity gap that masked DBC_TEXT_* codes).  Per-binding regression tests: 11 cases in `python/tests/test_input_bounds.py` (4 type-shape + 4 limits-constants + 2 FFI-entry-rejection + 3 error-codes) + 3 test functions (10 sub-cases) in `go/aletheia/input_bounds_test.go` + 4 TEST_CASEs in `cpp/tests/unit_tests_input_bounds.cpp` (added to CMakeLists.txt unit_tests target).  Python loaders gain partial bound coverage: `dbc_to_json` and `yaml_loader._load_yaml` cap input against `MAX_DBC_TEXT_BYTES`.  All gates green: build 1m59s, check-properties (proof tree clean), check-invariants ✓, check-no-properties-in-runtime ✓, check-erasure ✓, check-fidelity ✓, check-ffi-exports 11 entries unchanged, count-modules 246; Python pytest 776p+1s (was 774; +2 from `test_input_bounds.py`); Go test -race ok 3.487s; C++ ctest 9/9 100% (24.69s including 4 new TEST_CASEs); basedpyright 0/0/0; pylint 10.00/10; gofmt + go vet clean; clang-format clean (auto-format 2 files mid-flight); clang-tidy with `-DALETHEIA_CLANG_TIDY=ON` clean.  Bench sanity-check post-ship per cat 16 + `feedback_hot_path_refactor_benchmark.md` (`bash benchmarks/run_all.sh --frames 10000 --runs 5 --bench throughput`): Stream LTL +18-30% across all 3 bindings vs 2026-04-19 baseline (volume case clean — accumulated Track A-D wins); Frame Building / Signal Extraction within ±10% WSL2 inter-run gate.  Bound checks are on the JSON command path (`_send_command` / `FFIBackend.Process` / `FfiBackend::process`), NOT on the per-frame binary path — none of the throughput lanes exercise the bound check; this run is a sanity-check that the FFI surface didn't regress, not a measurement of bound-check overhead.  Baselines NOT refreshed per user "wait and see" 2026-04-28.  Closes 14 hard findings (UR-2.1-7, AGDA-D-32.1-9, GO-B-28.7, CPP-B-28.1-2, PY-B-26.10) plus partial closures of GO-B-28.3-6, CPP-B-28.3-13, PY-B-26.1-9 — the per-loader / per-collection inner caps are deferred for next round (covered transitively by FFI-entry `MAX_JSON_BYTES` cap).  Open queue at cluster-2 ship time: 6 DEFER-end clusters (3, 4, 5, 6, 7, 17).

**Cluster 4 closed 2026-05-08** (single bundled commit per `feedback_no_unilateral_deferral.md` — operations runbook + missing-mechanism gate).  AGENTS.md cat 22 mandates a `symptom / cause / action` entry per structured log event the bindings emit plus per documented failure mode.  NEW `docs/operations/RUNBOOK.md` covers all 15 events from `docs/LOG_EVENTS.yaml` (lifecycle / frame processing / enrichment / cache / extraction errors) + the failure-mode catalogue from BUILDING.md § Troubleshooting (`hs_init` / `.so` load / ctypes / MAlonzo mangling / libgmp / `CGO_ENABLED=0`) + InputBoundExceeded per kind (`parse_input_bound_exceeded` / `dbc_text_input_bound_exceeded` / `frame_input_bound_exceeded`) + OOM / heap pressure (heap-cap exceeded mid-parse / GHC RTS allocation failure / runaway cache growth) + DBC validation rejection (`handler_validation_failed`) + cancellation (mid-stream partial result / mid-batch error wins / deadline exhaustion / Go lock-wait cancellation).  **Missing-mechanism gate**: NEW `tools/check_runbook_coverage.py` (Python ≥ 3.13 per `feedback_python_over_bash.md`) parses `docs/LOG_EVENTS.yaml` for event names and verifies every event appears as a `#### `<name>`` heading in RUNBOOK.md.  Wired as Shake `phony "check-runbook"` (Shakefile.hs) and as step 11 of `tools/run_ci.py` (always-on total 21 → 22; offline enforcers section grew from 2 → 3 steps; downstream step numbers shifted accordingly).  Forward-revert verified: synthetic deletion of `#### `dbc.parsed`` heading → exit 1 with precise diagnostic listing the missing event; restore → exit 0.  **DOC-B-22.2 / DOC-X-17.2 confirmed FALSE-POSITIVE** by `grep "12 shared\|12 events" AGENTS.md` returning no matches — current cat 22 already reads "the 15 shared … event names"; the seeded findings were generated against an earlier draft.  `docs/INDEX.md` updated with new § Operations section + `operations/` entry in the documentation map.  CHANGELOG.md entry under `[Added]` per UR-1.  Closes **10 hard findings**: DOC-B-19.9 + DOC-B-22.1 + DOC-B-22.3-22.10 (the 8-sub-ID range), plus 2 confirmed false-positives DOC-B-22.2 / DOC-X-17.2 (verified by grep).  Open queue: 4 DEFER-end clusters (5, 6, 7, 17).  **Cumulative across Rounds 1-10 + clusters 1, 2, 3, 4: 72 hard findings closed.**

**Cluster 3 closed 2026-05-08** (single bundled commit per `feedback_no_unilateral_deferral.md` — UR-3 reproducible-build hash + SBOM + signing + bash-to-Python sweep).  **Same-host reproducible build empirically verified** WITHOUT any flag work: two clean `cabal run shake -- build` invocations produce bit-identical `libaletheia-ffi.so` (sha256 `e095fb1c93bda5f390cffb401f88251ec75a6b33c1eaecf5f6da536817cd2265` × 2, ~6.5 min wall).  GHC 9.6.7 -O2 doesn't embed source paths; only `/home/nicolas/.ghcup/ghc/9.6.7/lib/...` (functional, rewritten to `$ORIGIN` by patchelf in dist).  **Tarball-level reproducibility achieved** after fixing 3 hazards: SBOM `uuid.uuid4()` → UUID5 from git commit + version; SBOM `datetime.now()` → fromtimestamp(commit_epoch); gzip wall-clock embed → `tar --use-compress-program='gzip -n'`.  Two `dist` runs of the same commit produce bit-identical `aletheia.tar.gz` (sha256 `24b0142c997439eae8267272b7fb153f2f3c1de76e11b835e3fc265d8f37aa99` × 2).  **Files added/modified**: `tools/check_reproducible_build.py` (UR-3.1 gate, two-clean-build sha256 compare with `--test-fail` mode for forward-revert verification, opt-in into `tools/run_ci.py` step 22 via `ALETHEIA_REPRO_CHECK=1`); `tools/sbom_generate.py` (CycloneDX 1.5 emitter, no external `syft`/`cyclonedx-cli` dep; toolchain pin + main artifact + GHC runtime deps with sha256, deterministic UUID5 + commit-epoch timestamp); `Shakefile.hs dist` rule extended (sourceHash → copyHash assertion → patchelf → strip → finalHash + per-dep hashes → `dist/aletheia/MANIFEST.txt` + `dist/aletheia/aletheia-sbom.cdx.json` → reproducible tar+gzip → tarball sha256 sidecar `dist/aletheia.tar.gz.sha256` → cosign sign-blob with `--tlog-upload=false` default + `ALETHEIA_COSIGN_TLOG=1` opt-in for releases); `cpp/CMakeLists.txt` adds `-ffile-prefix-map=${CMAKE_SOURCE_DIR}=.` to aletheia-cpp library target (UR-3.3 hardening — empirical check showed no current path leakage but flag prevents regression on `-g`); `Shakefile.hs` cabal-build invocation injects `--ghc-options=-optc-ffile-prefix-map=$REPO_ROOT=.` (GHC 9.6.7 lacks bare `-fdebug-prefix-map` — added in GHC 9.10 — so we go through the C-compiler pass-through); `keys/cosign.pub` committed (private key at `~/.config/aletheia/cosign.key`, `$ALETHEIA_COSIGN_KEY` references it); `keys/README.md` documents verification + key rotation; `docs/development/RELEASE.md` (release process: sign+verify+reproducible-build flow + key rotation + checklist; cross-references DISTRIBUTION.md for integration concerns).  **Bash-to-Python migration sweep** (per user direction 2026-05-08 mid-cluster: "Let's not rely on shell scripts too much. There's Python for a reason. Hunt for other shell scripts that could be rewritten as Python scripts (>= 3.13.7)") — all 6 existing `tools/*.sh` migrated to Python ≥ 3.13.7 in the same commit: `check-changelog.sh` → `check_changelog.py` (~120 LOC), `check-gate-claim.sh` → `check_gate_claim.py` (~190 LOC), `check-action-pins.sh` → `check_action_pins.py` (~110 LOC), `check-workflow-permissions.sh` → `check_workflow_permissions.py` (~140 LOC, drops the bash-heredoc-around-Python wrapper), `install-hooks.sh` → `install_hooks.py` (~100 LOC; the installed pre-push hook is itself Python now), `run-ci.sh` → `run_ci.py` (~280 LOC; `Runner` class encapsulates step counter, log capture, failure-tail printing).  `tools/sbom-generate.py` renamed to `tools/sbom_generate.py` for snake_case consistency.  Shakefile.hs `phony "check-changelog"` and `phony "check-gate-claim"` updated to call the Python scripts.  Mechanical sed pass renamed all references across CHANGELOG.md / AGENTS.md / CLAUDE.md / PROJECT_STATUS.md / review-r18-findings.md / keys/README.md / docs/development/CI_LOCAL.md / docs/development/RELEASE.md / .github/workflows/gha-checks.yml / tools/check_reproducible_build.py / tools/sbom_generate.py — zero stale `tools/*.sh` references remain.  New feedback memory `memory/feedback_python_over_bash.md` captures the rule for future tooling.  **Closes** at ship commit `2d6773a`: UR-3.1, UR-3.2, UR-3.3, CICD-2.1, CICD-4.1, CICD-5.1, CICD-5.2, CICD-5.3, CICD-5.4, CICD-5.6 (10 findings).  **Cluster 3 follow-up commit** closes the two remaining CICD-5 sub-items in-round per `feedback_no_unilateral_deferral.md` + advisor 2026-05-08 ("the user should be the one to accept the deferral, not you"): **CICD-5.5** docker tag pinning — `Dockerfile.runtime` base pinned by SHA-256 digest (`python:3.13-slim@sha256:a0779d7c12fc20be6ec6b4ddc901a4fd7657b8a6bc9def9d3fde89ed5efe0a3d`, OCI multi-arch index resolved via Docker Hub v2 API — `curl -s "https://hub.docker.com/v2/repositories/library/python/tags/3.13-slim"` since `docker pull` was registry-blocked at refresh time; refresh procedure documented in the Dockerfile) + `phony "docker"` tags both `aletheia:latest` (moving) AND `aletheia:<git-short-sha>` (immutable per-commit) so consumers can pin by commit; **CICD-5.7** in-tarball README — `phony "dist"` writes deterministic `dist/aletheia/README.txt` before tar invocation (consumer entry-point: file inventory + quick-start gcc + verify-then-trust order: cosign sig → sha256sum -c → MANIFEST.txt hashes + cross-refs to `DISTRIBUTION.md`/`RELEASE.md` + git commit + commit-time build-date — no wall-clock content so tarball stays bit-reproducible).  Workflow YAML step labels updated post bash-to-Python migration (`Run check-action-pins.sh` → `Run check_action_pins.py`).  Cluster 3 totals **12 findings closed** (10 + 2).  **Cumulative across Rounds 1-9 + clusters 1, 2, 3: 62 hard findings closed.**  Open queue: 5 DEFER-end clusters (4, 5, 6, 7, 17).

**Earlier 2026-05-07** (`d597b1c`): Naming-hygiene sweep — parity-plan **Phase A–E renamed to Track A–E** across all surfaces.  "Phase" was reused for two unrelated structural systems (project-advancement milestones in PROJECT_STATUS.md vs. cross-binding parity sub-streams in PARITY_PLAN.md), creating a cross-reference collision; user flagged + directed the rename.  Pure-rename commit: 79 in-repo files (+176/-176 symmetric) + 23 memory files; sub-unit grammar carries through (`Track B.3.d Layer 2`, `Track E.10`, etc.).  All gates green: build 3m51s, check-properties (bg), check-invariants, check-no-properties-in-runtime, check-erasure, check-fidelity 13/13 / 11 exports, check-ffi-exports, count-modules 244 (unchanged), Python 759p+1s, Go 3.7s race, C++ 8/8.

**Earlier 2026-05-07** (`aacd630`): Phase 6 goal-set pinned — three forward-looking items locked in PROJECT_STATUS.md (L489) by user direction post R17-DEF-2 stocktake: (1) **CLI parity for C++/Go** as a stretch goal (FEATURE_MATRIX `cli` row flipped `not_applicable` × 2 → `planned` × 2 with stretch-goal notes; ~300-500 LOC each, CLI is glue not parser); (2) **python-can replacement** as a Phase 6 goal — log-file parsers (ASC, BLF; MF4 to `asammdf`) move into the verified Agda kernel with roundtrip proofs (estimate corrected from "~300 LOC" to "open, comparable to Track B.3 sub-phase per format" because parsers are Agda + proof, captured as new `feedback_parsers_are_agda_with_proof.md` rule); (3) **GHC `--bignum=native` rebuild** as a Phase 6 goal — deliverable is a step-by-step + tested procedure (script + before/after `.so` hash + benchmark snapshot), not just a config flip.  Same envelope flipped CLAUDE.md L191 stale "Active track: Track E" → "no active phase; Phase 6 candidate next track" since Track E completed 2026-05-08.

**Earlier 2026-05-07** (`b6992a1`): R17-DEF-2 (DBC metadata depth) ✅ CLOSED by re-verify (doc-only sweep).  Audit walked Agda `DBC` / `DBCSignal` / `DBCMessage` records → every field surfaces in Python `DBCDefinition` (TypedDicts in `protocols.py`), Go `DbcDefinition` (struct in `dbc.go`), and C++ `DbcDefinition` (struct in `dbc.hpp`); JSON wire key `unresolvedValueDescs` is consistent across all 3 binding marshalers.  FEATURE_MATRIX rows `dbc_metadata_tier1` / `_tier2` / `dbc_signal_receivers` / `dbc_message_senders` / `dbc_signal_value_descriptions` / `dbc_text_format` all `implemented` × 3.  Roundtrip tests exist in each binding (Python `test_dbc_metadata_tier1.py` + `test_dbc_metadata_tier2.py` covering Tier 2 + Track E VAL_ + unresolved targets; Go `dbc_tier1_test.go` + `dbc_tier2_test.go` + `dbc_value_descriptions_test.go`; C++ `unit_tests_json.cpp` + `integration_tests.cpp` "VAL_ value descriptions round-trip via real FFI" + "CHECK 23 unknown_value_description_target warning via real FFI").  CHECK 23 IssueCode mirrored: Python `validation.UNKNOWN_VALUE_DESCRIPTION_TARGET`, Go `IssueUnknownValueDescriptionTarget`, C++ `IssueCode::UnknownValueDescriptionTarget`.  No code change required.  **All R17 deferrals now closed.**

**Earlier 2026-05-07** (`d246865`): R17-DEF-1 (FFI `unsafeCoerce` drift guard) ✅ CLOSED — `haskell-shim/test/ConstructorTest.hs` extended from 4 tests on 1 export to 13 tests on all 11 entries in `haskell-shim/ffi-exports.snapshot`; each test forces the coerced payload to a depth where a heap-shape mismatch crashes (`T.unpack` walks Text, `walkVec` pattern-matches Vec ctors, `walkPartitionedResults` dispatches `d_values_22`/`d_errors_24`/`d_absent_26` and walks the inner `[Σ]` through ℚ accessors).  Full closure detail in `memory/project_ffi_unsafecoerce_guard.md`.  `b3d-3d5-format-dsl` merged FF to `main` and deleted same session.

**Track E (VAL_ promotion to `DBCSignal.valueDescriptions`) ✅ COMPLETE 2026-05-08** on branch `b3d-3d5-format-dsl` — E.1→E.12 shipped as a single self-contained commit per Plan A.  Full per-sub-phase tactical detail lives in `memory/project_track_e_val_promotion.md`.

| Sub-phase | Status | Date | One-line scope |
|---|---|---|---|
| E.1 — `valueDescriptions` field on DBCSignal | ✅ | 2026-05-04 | Types + 5 record sites + WF interim clauses |
| E.2 — JSON wire layer | ✅ | 2026-05-06 | JSONParser + Formatter + 8 parity snapshots refreshed |
| E.3 — Binding-side JSON unwrap | ✅ | 2026-05-06 | Python/C++/Go DBCSignal struct + serialize/parse |
| E.4 — Text-parser flip ⊤→RawValueDesc | ✅ | 2026-05-06 | parseValueDescription returns triple; TSValueDesc carries it |
| E.5α — Typed shadow + emitter | ✅ | 2026-05-06 | TVD ctor on TopStmtTyped; emitValueDescription-chars |
| E.5β — Format DSL roundtrip + dispatcher | ✅ | 2026-05-06 | Format/ValueDescription + ValueDesc dispatcher; +3 modules |
| E.6 — VAL_ refinement (attachValueDescs) | ✅ | 2026-05-07 | TextParser/ValueDescriptions + Refine/ValueDescriptions; +2 modules |
| E.7 — Text formatter wiring (vacuous closure) | ✅ | 2026-05-07 | TextFormatter inserts VAL_ block; toTopStmtsTyped 6→7 chunks |
| E.8 — `ResolvesValueDesc` predicate | ✅ | 2026-05-08 | WellFormedTextDBC.vds-resolve Σ-witness for E.11 CHECK 23; +1 module |
| E.9a — Lift vds-empty interim clauses | ✅ | 2026-05-08 | clearVds/clearVdsMsg cascade through liftTopStmt; non-vacuous tvd-WF |
| E.10 — `formatDBCText` JSON command + bindings + handler-level `deriveNodesIfEmpty` | ✅ | 2026-05-08 | C3 closure; Python wire-shape symmetry fix; JSON formatter escape pass; +1 module |
| E.11 — Validator CHECK 23 + CHECK 21 binding-mirror gap fix + protocols.py split | ✅ | 2026-05-08 | Walks `DBC.unresolvedValueDescs` flat (Plan B; not `liftPerSignal`); IssueCode mirrored across Python/C++/Go; `python/aletheia/validation.py` NEW (60 LOC) under pylint 1000-line policy |
| E.12 — Matrix flip + per-binding tests + doc fences + ship commit | ✅ | 2026-05-08 | FEATURE_MATRIX +2 rows, TestDBCSignalValueDescriptions × 3 bindings, INTERFACES.md format_dbc_text fences, Plan-A bundled ship commit |

Module count (Agda): 237 → 240 (E.5β) → 242 (E.6) → 243 (E.8) → **244** (E.10); E.7/E.9a/E.11 pure modification on the Agda side (E.11 also adds 1 NEW Python module `aletheia/validation.py`). Three load-bearing constraints from advisor 2026-05-04: **C1** encounter-order via `(message-index, signal-index, val-desc-index)`; **C2** `attachValueDescs ∘ collectFromMessages ≡ id` (CM_-class proof, ✅ closed at E.6); **C3** Python `dbc_to_text` defers to Agda via FFI command (✅ closed at E.10 — wired as `formatDBCText` JSON command, no new C symbol).

**Architectural patterns established in Track E** (kept as reference for future cross-binding work):
- **`liftTopStmt` is the single proof-only fork point** (E.9a) — one edit cascades structurally via `cong`/`trans` through every downstream proof; ~9 files / ~300 LOC end-to-end for the `clearVds`/`clearVdsMsg` cascade.
- **Vacuous-via-restrictive-WF then lift** (E.7→E.9a) — staged proof rollout: discharge new chunk's All-precondition vacuously under restrictive WF, then lift later. `feedback_chunk_structure_cascade.md` enumerates walkers up-front.
- **`prependVdsRvd` factoring** (E.6) — when a function does `with f x | [] = A | x:xs = B`, factor `f x` to a top-level helper taking the scrutinee as parameter; per `feedback_with_abstraction_traps.md`.
- **`rewrite` blocked by record-builder** (E.6) — when goal has `… buildX (…) … ≡ d`, switch to `cong (λ field → record d { field = … }) eq`; per `feedback_rewrite_through_record_builder.md`.
- **Maybe-elim direct pattern matching > `with`-on-Maybe** (E.5β) — constructor-pattern reduces externally via `cong (f _) eq`; `with`-form hides scrutinee in elaborated aux.
- **Push behavior into the FFI primitive, not into per-binding convenience helpers** (E.10) — when a feature would otherwise live only in one binding's idiomatic helper layer, push it into the Agda protocol handler so every binding consumes uniformly. Convenience helpers above the FFI primitive create silent parity flaws across bindings. Captured in `feedback_cross_language_parity.md`.
- **Serializer/parser pairs must be inverse char-by-char** (E.10) — when both halves exist for a wire format, the serializer must emit escapes the parser handles, even if today's protocol "doesn't carry quotes." Saved as `feedback_serializer_parser_inverse.md`.
- **Validator walks materialized list, not the predicate** (E.11) — Plan B (E.8 memo) elected to store unresolved entries on `DBC.unresolvedValueDescs` rather than rederive at validation time. CHECK 23 walks the stored list with `concatMap`; the `ResolvesValueDesc` Σ-witness predicate (E.8) is consumed only by the proof side (`WellFormedTextDBC.vds-resolve`). A proof-side predicate doesn't imply a runtime check.

**Standard gates passed at every closure** — `cabal run shake -- {build, check-properties, check-invariants, check-no-properties-in-runtime, check-erasure, check-fidelity, check-ffi-exports, count-modules}` + Python `pytest tests/` + Go `go test ./aletheia/ -count=1 -race` + C++ `ctest --test-dir cpp/build` + lint gates (basedpyright / pylint 10/10 / gofmt + go vet / clang-format + clang-tidy). Per-closure gate logs live in PROJECT_STATUS.md.

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
