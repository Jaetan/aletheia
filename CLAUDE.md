# CLAUDE.md

Guidance for Claude Code (claude.ai/code) when working in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). Core logic in Agda with correctness proofs, compiled to Haskell, exposed through Python, C++, and Go APIs. Phase status: [PROJECT_STATUS.md](PROJECT_STATUS.md). Mission: [docs/PITCH.md](docs/PITCH.md).

## Development Environment

**Must be preserved across session compression.**

- Agda binary: `/home/nicolas/.cabal/bin/agda`
- Shell: `/usr/bin/fish` (config at `/home/nicolas/.config/fish/config.fish`)
- User binaries: `/home/nicolas/.local/bin`; libraries: `/home/nicolas/.local/lib`

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

244 total modules (`cabal run shake -- count-modules`):
- **239**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer — co-located here to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

243 of 244 modules use `--safe`. No modules require `--sized-types`. Per-commit module-count drift (Path A.4 cluster lift, Phase E sub-phase additions, etc.) is recorded in PROJECT_STATUS.md and `memory/project_b3d_universal_proof.md` / `memory/project_phase_e_val_promotion.md`.

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
- **DBC validation rejection**: check `ValidationIssue.code` enum — table in [PROTOCOL.md § Common Error Codes](docs/architecture/PROTOCOL.md#common-error-codes). `aletheia validate --dbc <file>` to see all issues.
- **Property formula parse error**: JSON schema is strict (`"operator"` lowercase, predicates under `{"operator": "atomic", "predicate": {...}}`). Compare against `Signal("X").equals(1).to_dict()` output.

## Performance Considerations

- **Parser combinators**: structural recursion on input length, not fuel — fuel breaks termination or blows up type-checking. See `Parser/Combinators.agda`.
- **Type-checking**: always `+RTS -N32 -RTS` (StreamState/Main otherwise time out past 120s).
- **Hot path**: `Dec`-valued predicates allocate proof terms per call in MAlonzo. Replace with `Bool`-valued fast path + equivalence lemma. See `extractSignalCoreFast` for the pattern.

## Implementation Phases

[PROJECT_STATUS.md](PROJECT_STATUS.md). Current state: Phase 5.1 complete (binary FFI 4.3× CAN 2.0B / 9.1× CAN-FD; CAN-FD; C++/Go bindings; cross-language benchmarks; four-tier check interface with full parity). Active track: Phase E (VAL_ promotion to `DBCSignal.valueDescriptions`).

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

For full history (R6–R17, Path G, Phase 5.1, Phases A/B.1–B.3, B.3.d Layers 1–4, Phases C/D) see [PROJECT_STATUS.md](PROJECT_STATUS.md). Per-commit narratives + sub-phase tactical detail live in PROJECT_STATUS.md, `memory/project_b3d_universal_proof.md`, and `memory/project_phase_e_val_promotion.md`. Resume notes / next-session entry point: [.session-state.md](.session-state.md).

**Current track:** Phase E (VAL_ promotion to `DBCSignal.valueDescriptions`) ✅ COMPLETE 2026-05-08 on branch `b3d-3d5-format-dsl` — E.1→E.12 shipped as a single self-contained commit per Plan A.  Full per-sub-phase tactical detail lives in `memory/project_phase_e_val_promotion.md`.

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

**Architectural patterns established in Phase E** (kept as reference for future cross-binding work):
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

- **Phase D ✅ COMPLETE 2026-05-04** — cross-binding doc-example harness (Python `pytest --markdown-docs` + Go `TestDocExamples` + C++ Catch2 `doc_example_tests`); R17-DEF-6 closed by D.2 `d0ae26b` + D.1 `82d0347`. Every ```cpp``` / ```go``` / ```python``` fence in tracked markdown files runs end-to-end against the real Agda core; harness immediately surfaced multiple dead doc API references.
- **Phase C ✅ COMPLETE 2026-05-03** — cancellation contract bound across all 3 bindings: C.0 SSOT `05108cf` + C.3 Go ctx `eef9dcc` + C.4 C++ stop_token `ef1292d` + C.1+C.2 Python async + send_frames_iter `c8ab95b`. Cancel at FFI boundaries; commit-prefix-and-report; behavioral parity by language idiom. FEATURE_MATRIX `cancellation_contract`/`lazy_streaming_batch` × 3 rows flipped. See `memory/project_async_api_phase6.md`.
- **Phase B.3 ✅ COMPLETE 2026-05-03** — universal roundtrip (B.3.d `bca99f2`) + JSON binding + ParsedDBCResponse + C++/Go bindings (B.3.e/h/i `bc7a5fc`) + cross-binding parity gate (B.3.j `3673cd2`+`3404dec`) + Python migration to verified parser (B.3.f `019d014`) + cantools dropped (B.3.g `2daa2fb`). LGPL contingency for cantools fully realised.
- **B.3.d universal target** — `∀ d → WellFormedDBC d → parseText (formatText d) ≡ inj₂ d` proven in `Substrate/Unsafe.agda` (sole axiom consumer; co-located by Unsafe-module policy — see `memory/feedback_unsafe_module_policy.md`). Layer 3 fully migrated to Format DSL (BO_ / ValueTable / BU_ / EV_ / CM_ / Preamble / BA_DEF_* / BA_*); Layer 4a/4b/4c-(a)/(b)/E all closed.

## Format DSL toolkit (`DBC/TextParser/Format.agda`)

- **Core constructors**: `literal` / `ident` / `nat` / `stringLit` / `pair` / `iso` / `many` / `refined` / `altSum` / `withPrefix`.
- **Whitespace family** (each with distinct parser permissiveness — see `feedback_format_dsl_ws_family_discipline.md`): `ws` / `wsOpt` / `wsCanonOne` / `wsCanonTab` / `withWS` / `withWSOpt` / `withWSCanonOne` / `withWSCanonTab` / `withWSAfter`.
- **Refinement carriers**: `decRat` / `intDecRat` / `natDecRat`.
- **Sugar**: `discardFmt` (wire-only fields) / `nonNewlineRun` (opaque-tail consumer) / `newlineFmt` (LF/CRLF).
- **Cycle-break pattern**: when a Format module would close a cycle, extract cycle-relevant subset to a `Foundations.agda` submodule (used at 3d.5.c-ε / 3d.5.d-3c-A).

## Performance baseline

Path A profile (post-3d.4 + JSON-mirror, runtime impact retained from `320c5a9`): Stream LTL +12-38% across bindings (Bool fast path); Signal Extraction -2-9% / Frame Building -1-7% (Path A structural cost). All 3d.5+ Format DSL work + Phase E sub-phases are proof-only and runtime-neutral on the streaming hot path. Baselines NOT refreshed per user "wait and see" 2026-04-28; COMPILE-pragma escape hatch deferred (requires explicit user approval per `feedback_no_suppression_without_approval`).

**Cross-binding parity roadmap**: [docs/development/PARITY_PLAN.md](docs/development/PARITY_PLAN.md), locked after R17. Active deferrals (R17-DEF-1..5; R17-DEF-6 closed by Phase D) tracked in `memory/project_*.md`.
