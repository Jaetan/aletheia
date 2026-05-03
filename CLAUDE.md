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

237 total modules (`cabal run shake -- count-modules`):
- **232**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer (post-Layer 4c task E, 2026-05-03) — co-located in this single module to keep the trusted-axiom-consuming surface at one allowlisted module by name (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

236 of 237 modules use `--safe`. No modules require `--sized-types`. Path A.4 (3d.4 + JSON-mirror, 2026-04-27) lifted the prior 47-module `--without-K`-only cluster to `--safe --without-K` by retyping `Identifier.name`, JSON `JString`, DBC AST text fields, and LTL signal names from `String` to `List Char`. Per-commit module-count drift since 3d.5 is recorded in PROJECT_STATUS.md and `memory/project_b3d_universal_proof.md`.

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

[PROJECT_STATUS.md](PROJECT_STATUS.md). Current state: Phase 5.1 complete (binary FFI 4.3× CAN 2.0B / 9.1× CAN-FD; CAN-FD; C++/Go bindings; cross-language benchmarks; four-tier check interface with full parity). Active track: Phase B.3.d.

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

**Pre-commit minimum** (doc-only changes): `agda +RTS -N32 -RTS src/Aletheia/Main.agda` → `cabal run shake -- build` → relevant binding tests. For code changes, [AGENTS.md § Step 4](AGENTS.md#step-4-implement-and-verify) defines the canonical 4-gate sequence (Agda build → unit tests → lint gates → benchmarks); do not let this section drift from it.

**Resources**: [Agda Documentation](https://agda.readthedocs.io/), [Standard Library](https://agda.github.io/agda-stdlib/), [Agda Tutorial](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html).

---

## Current Session Progress

For history (R6–R17, Path G, Phase 5.1, Phases A/B.1/B.1.x/B.2/B.3.a-c, B.3.d pre-gate, Layers 1–2, Layer 3 commits 3a/3b/3c.0–3c.4/3d.1–3d.3) see [PROJECT_STATUS.md](PROJECT_STATUS.md). Per-commit narratives for 3d.4–3d.8 + 3d.5.a–3d.5.d sub-phases live in [PROJECT_STATUS.md](PROJECT_STATUS.md) and [memory/project_b3d_universal_proof.md](memory/project_b3d_universal_proof.md). Resume notes / next-session entry point: [.session-state.md](.session-state.md).

**Current track:** Phase C ✅ COMPLETE 2026-05-03 on branch `b3d-3d5-format-dsl` — cancellation contract bound across all three bindings; FEATURE_MATRIX `cancellation_contract` × 3 + `lazy_streaming_batch` × 3 rows all flipped.

**Status (2026-05-03): Phase C COMPLETE.**  Four ship commits: `05108cf` (C.0: `docs/architecture/CANCELLATION.md` SSOT — cancel at FFI boundaries; commit-prefix-and-report; behavioral parity by language idiom) → `eef9dcc` (C.3: Go `context.Context` as first parameter on every Client operation method; `sync.Mutex` replaced with a 1-deep `chan struct{}` semaphore so ctx cancellation can abandon the lock wait via `select { case <-lockCh: ...; case <-ctx.Done(): return ctx.Err() }`) → `ef1292d` (C.4: C++ `std::stop_token` as first parameter on every Client operation method; new `ErrorKind::Cancellation` value; pre-FFI guards via `if (stop.stop_requested()) [[unlikely]]` — the `[[unlikely]]` cold-path attribute reclaims ~4% Stream LTL otherwise lost to the new branch) → `c8ac95b` (C.1+C.2: Python `aletheia.asyncio.AletheiaClient` mirrors sync surface method-for-method via `asyncio.to_thread` (17 async methods); new sync `AletheiaClient.send_frames_iter` generator yields `FrameResult` per frame — consumer `break` / `gen.close()` lands the commit-prefix-and-report contract on the sync side; new `SignalOpsMixin(ABC)` extracts `extract_signals` / `update_frame` / `build_frame` to keep `_client.py` under the 1000-line pylint threshold per `feedback_no_weak_config_bumps.md`).  **Cross-binding asymmetry locked in**: `BatchError.partial_results` (Python) carries the committed prefix on **non-cancellation errors only** — sync `send_frames` matches Go `BatchResult.responses` + C++ batch result (full prefix), sync `send_frames_iter` is `[]` (every committed result already yielded), async cancellation propagates `asyncio.CancelledError` verbatim (BaseException since 3.8 → not caught by `except Exception`).  **Bench verification** per `feedback_hot_path_refactor_benchmark.md` (4-batch comparison, 2× C.4 baseline + 2× C.1+C.2): system noise high today (Python lanes drift -14% Stream LTL batch-to-batch with no source changes); averaged Python deltas Stream LTL **-4.7%**, Signal Extraction **-1.6%**, Frame Building **+0.3%**; C++/Go on unchanged `.so` showed comparable inter-batch drift, confirming noise-floor and no mixin-MRO regression.  **Module count unchanged at 237** — no Agda module changes in Phase C; the entire phase is binding-side ergonomics over the existing FFI surface.  See `memory/project_async_api_phase6.md` for design + implementation post-mortem.  Active branch: `b3d-3d5-format-dsl`.

**Status (2026-05-03): Phase B.3 COMPLETE.**  Final ship sequence: B.3.d (`bca99f2`, universal roundtrip theorem) → B.3.e/h/i (`bc7a5fc`, JSON binding + ParsedDBCResponse envelope + C++/Go bindings) → B.3.j (`3673cd2` + `3404dec`, cross-binding corpus parity gate + native canonical wire form) → B.3.f (`019d014`, Python `dbc_to_json` flipped to verified Agda parser; surfaced + fixed two Python-side parity asymmetries: `parse_parsed_dbc_response` now runs `normalize_dbc` so callers see `Fraction` rationals, `FractionJSONEncoder` canonicalised to "emit int when denominator=1") → B.3.g (`2daa2fb`, cantools fallback dropped outright; ~3,560 net LOC removed; `[dbc]` extra retired from `pyproject.toml`).  All three bindings (Python `dbc_to_json` / `parse_dbc_text`, C++ `parse_dbc_text`, Go `ParseDBCText`) now run on the verified Agda parser with B.3.d's universal roundtrip underwriting them; `examples/example.dbc` lost a stray trailing space after `NS_ :` so the strict Agda parser accepts it.  Module count unchanged at **237** post-B.3.e (B.3.f/g/j were Python-side / binding-side / docs only).  LGPL contingency for cantools fully realised.  Lessons captured: `feedback_cross_binding_wire_symmetry.md` (NEW — every wire-shape rule must apply at every binding's serializer AND deserializer; B.3.f/B.3.j surfaced two Python-side asymmetries) + `feedback_heavy_import_handler_split.md` (B.3.e — handler-import-closure heap blowup).  Active branch: `b3d-3d5-format-dsl`.

**Status (2026-05-03): Phase B.3.d COMPLETE.**  Universal target

    ∀ d → WellFormedDBC d → parseText (formatText d) ≡ inj₂ d

proven in `Substrate/Unsafe.agda` (sole consumer of the two stdlib-equivalent bridging axioms; co-located with the axioms by Unsafe-module-policy — see `memory/feedback_unsafe_module_policy.md`).  Layers 1–2 ✅; Layer 3 ✅ (all per-line constructs migrated to Format DSL); Layer 4a ✅ (`70766cd`) + 4b ✅ (`7b17da6`) + 4c-(a) ✅ (`cf091d8`) + 4c-(b) ✅ (`6c7ade3`) + 4c task E ✅ (`bca99f2`, 2026-05-03) — closes B.3.d.  Path A.4 (3d.4 + JSON-mirror, commit `320c5a9` on `b3d-3d4-json-detaint`) lifted the prior 47-module `--without-K`-only cluster to `--safe --without-K` and shipped Path A.5 Bool fast path on `Cache.lookupEntries` / `DBCHelpers.findSignalInList`.

**Layer 3 construct status** (✅ migrated to Format DSL via η-style wrap `parse <leafFmt> >>= many parseNewline >>= …`; % = strict-LOC reduction on production-side):
- BO_ block ✅ — 3d.6 + 3d.7 + 3d.8 (commits `89e04ee` + `42228df` + `f25ca5a`); spine-based `emitMessage-chars-decompose` + 2-stage `pos-eq` patterns established here for future multi-line composers.
- ValueTable ✅ — 3d.5.d (`b374217`, 83%).
- BU_ ✅ — 3d.5.d-BU_ (`abc7d0f`, 73%).
- EV_ ✅ — 3d.5.d-EV_ (`21a3146`, 94%); introduced `discardFmt` (parse-permissive / emit-canonical) + `varTypeFmt` ADT-via-altSum-tree + iso patterns.
- CM_ ✅ — 3d.5.d-CM_ (`7c27100`, 88.6%; heaviest L3 at 2,533L pre-migration); introduced `shift-trail-space` ++ₗ-assoc bridge for `withWSAfter`-baked trailing-space slots; CAN-ID K-elim avoidance via `with buildCANId | buildCANId-rawCanIdℕ ; just .cid | refl = refl`.
- Preamble (VERSION / BS_ / NS_) ✅ — 3d.5.d-3a (`c5b34fb`, 76% combined; Namespace alone 91%); introduced `wsCanonTab` + `nonNewlineRun` DSL constructors; discard-iso pattern over `many nsLineFmt` for fixed-body emit; spec-drift catch via advisor (`withWSCanonOne` vs `withWS` parser permissiveness).
- BA_DEF_ / BA_DEF_REL_ ✅ — 3d.5.d-3c-A (`27aaa8c`, 56% combined / 82% Properties-side); deleted `Properties/Attributes/Type.agda` entirely; introduced `intDecRat` / `natDecRat` DSL constructors; cycle break via `Attributes/Foundations.agda`; 5-case-cong-bridge pattern (vs 25-case enumeration); `concatMap-foldr-bridge` structural induction.
- BA_ / BA_REL_ / BA_DEF_DEF_ ✅ — 3d.5.d-3c-B (`3ab805e`, 4% combined / 29% Properties-side); 7 Properties files refactored (Network/Node/Msg/Sig/EV/Rel/Default; 4044 → 2884 strict-LOC); new modules Format/AttrLine.agda + Format/AttrValue.agda + Properties/Attributes/Assign/Common.agda; specialized `parseAttrAssign-format-roundtrip-RatwNet` for inj₂-deep target position (avoids universal-lemma's L5 EmitsOK obligation that OOMs at -M16G); per-shape numeric dispatchers use **constructor pattern-match + `proj₁`/`proj₂` projections, NOT `with`** (the `with`-abstraction over wide ∃₂ × _⊎_ Σ-types triggers goal-rebuild thrash through inj₂-deep `EmitsOK` reduction even with hoisted helpers — 6+ min OOM → 13s after fix; see `feedback_with_abstraction_traps.md`).  `parseAttrLine` top-level dispatcher unchanged — its 5-way `<|>` chain consumes the migrated sub-parsers transparently.

**Layer 4 progress**:
- 4a ✅ — `Format/SignalGroup.agda` (last per-line construct migrated to DSL) + `Properties/CharClassDisjoint.agda` (4 owed bridge lemmas all discharged).
- 4b ✅ — `Properties/ManyRoundtrip.agda` (polymorphic `many-η-roundtrip` helper) + 5 list-level lifts (SignalGroups / ValueTables / EnvVars / Comments / Messages).
- 4c-(a) ✅ shipped `cf091d8` — parseTopStmt restructured to 7-bucket head-character pattern dispatch + 5 simple section dispatchers + generic `parseTopStmt-on-BA-head` Attribute helper.  TVT pilot validated pivot: 15.7 GB / 273s → 443 MB / 14s (35× memory).  Foundations + BodyBridge + many-η-roundtrip-with-lift extension shipped alongside.  Module count 209 → 218.
- 4c-(b) ✅ shipped `6c7ade3` — TAT universal attribute roundtrip via β prefix-lemma strategy.  3-way DBCAttribute dispatch routes through 31 existing parseAttrLine-roundtrip-* slims; per-shape `emit*-chars-BA-head` Σ-witness lemma + `parseTopStmt-on-BA-head-via-prefix` accept-input-and-prefix-witness lift.  7-case TopStmt scope dispatch 25 min OOM → 1-case via β 13.8s (≥120× speedup).  Module count 218 → 231 (+13).
- **4c task E ✅ shipped `bca99f2` (2026-05-03) — closes Phase B.3.d.**  Tasks B/C/D/E in one commit:
  - **B** `Aggregator/Dispatcher.agda` (TopStmtTypedWF + combined per-section dispatcher) + `Aggregator/ManyTopStmts.agda` (single application of many-η-roundtrip-with-lift); TAT case factors through β prefix witness for nonzero / head-not-newline.
  - **C** `Aggregator/Partition.agda` — partitionTopStmts-bridge: 6 per-section accumulator-style lemmas + 5 foldr-++ + cong-mkCollectedTop with 6 ++ₗ-identityʳ cleanups.
  - **D** `Aggregator/Refine.agda` — collectRawDefs-rawOf passthrough + refineAttributes-on-rawOf inverse.  Lifted `refineAll` from where-block to top-level in `Attributes.agda` so the inductive proof can address `defs ≢ collectRawDefs raws`.
  - **E** `Aggregator/Universal.agda` (`--safe`) — composes WellFormedDBC record + parseDBCText 5-step bind chain + parseTextChars-on-formatChars closure (split into stage 1 cong + stage 2 finalizeParse-on-mkResult-clean to bound rewrite scope; single-shot OOM'd at -M16G).  String-level `parseText-on-formatText` co-located in **`Substrate/Unsafe.agda`** by deliberate Unsafe-module policy (sole axiom consumer; see `memory/feedback_unsafe_module_policy.md`).  Walk-root coverage collapsed from 3 to 1 (`Substrate/Unsafe.agda`).  Module count 231 → 236 (+5, all `--safe --without-K`).

**Format DSL toolkit** (post-3c-A, in `DBC/TextParser/Format.agda`):
- Core constructors: `literal` / `ident` / `nat` / `stringLit` / `pair` / `iso` / `many` / `refined` / `altSum` / `withPrefix`.
- Whitespace family (each with distinct parser permissiveness — see `feedback_format_dsl_ws_family_discipline.md`): `ws` (parser one-or-more, canonical single space) / `wsOpt` (zero-or-more, canonical empty) / `wsCanonOne` (zero-or-more, canonical single space) / `wsCanonTab` (one-or-more, canonical tab) / `withWS` / `withWSOpt` / `withWSCanonOne` / `withWSCanonTab` / `withWSAfter`.
- Refinement carriers: `decRat` / `intDecRat` / `natDecRat`.
- Sugar: `discardFmt` (wire-only fields), `nonNewlineRun` (opaque-tail consumer), `newlineFmt` (LF/CRLF).
- Cycle-break pattern (3d.5.c-ε / 3d.5.d-3c-A): when a Format module would close a cycle, extract cycle-relevant subset to a `Foundations.agda` submodule.

**Path A profile** (post-3d.4 + JSON-mirror, runtime impact retained from `320c5a9`): Stream LTL +12-38% across bindings (Bool fast path); Signal Extraction -2-9% / Frame Building -1-7% (Path A structural cost). All 3d.5+ Format DSL work is proof-only and runtime-neutral on the streaming hot path — the migrated parsers (`parseSignalLine`, `parseValueTable`, `parseMessage`, `parseBU`, `parseEnvVar`, `parseComment`, `parseVersion`, `parseBitTiming`, `parseNamespace`, `parseAttrDef`, `parseAttrDefRel`, `parseRawAttrAssign`, `parseRawAttrRel`, `parseRawAttrDefault`) all run at DBC config time only. Baselines NOT refreshed per user "wait and see" 2026-04-28; COMPILE-pragma escape hatch deferred (requires explicit user approval per `feedback_no_suppression_without_approval`).

**Architectural plan locked 2026-04-26 (post-3d.3b) + amended 2026-04-27 (JSON-mirror addition)** per [PARITY_PLAN.md §B.3.d](docs/development/PARITY_PLAN.md):
1. 3d.4 + JSON-mirror + Path A ✅ shipped 2026-04-28 (`320c5a9`).
2. 3d.5 Format DSL framework: (a) framework core ✅; (b) single-construct validation gate ✅; (c) pinch-point extensions ✅ (α `refined` / β `altSum` + `withPrefix` / γ `CanonicalReceivers` / ε Topology split / ζ `decRat` + `ws`-family / η `parseSignalLine`); **(d) migration of remaining 3a–3d.3 proofs onto DSL ✅ COMPLETE:** ValueTable / BU_ / EV_ / CM_ / Preamble / BA_DEF_ / BA_/BA_REL_/Default. (e) renumbered 3d.6–3d.8 ✅. (f) Layer 4 aggregation: 4a ✅ / 4b ✅ / **4c-(a) ✅** (parseTopStmt head-dispatch + 5 simple dispatchers + Attribute helper) / 4c remaining: TAT universal + many-η-with-lift + partition + refineAttributes inverse + universal aggregator.

**Cross-binding parity roadmap**: [docs/development/PARITY_PLAN.md](docs/development/PARITY_PLAN.md), locked after R17. Active deferrals (R17-DEF-1..6, B.3.d Layer 4 owed lemmas, B.3.d-gated cantools drop) tracked in `memory/project_*.md`.
