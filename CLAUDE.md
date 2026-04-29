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

199 total modules (`cabal run shake -- count-modules`):
- **194**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) used only by the outer `parseText/formatText` wrap in DBC (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

198 of 199 modules use `--safe`. No modules require `--sized-types`. 3d.5 Format DSL (2026-04-27) added 2 modules (`DBC/TextParser/Format.agda` + `DBC/TextParser/Format/ValueTable.agda`), both `--safe --without-K`. 3d.5.c-γ (2026-04-28) added 3 more (`DBC/CanonicalReceivers.agda` + `DBC/TextParser/Format/Receivers.agda` + `DBC/TextParser/Format/Receivers/Roundtrip.agda`), all `--safe --without-K`. 3d.5.c-ε (2026-04-28) added 2 more by splitting `Topology.agda` into `DBC/TextParser/Topology/Foundations.agda` (cycle-relevant subset: CANID + mux primitives) + `DBC/TextParser/Topology/SignalLine.agda` (BU_/SG_/BO_ machinery), keeping `Topology.agda` as a re-export facade — all `--safe --without-K`. 3d.5.c-η (2026-04-28) added 2 more (`DBC/TextParser/Format/SignalLine.agda` + `DBC/TextParser/Format/SignalLine/Roundtrip.agda`), both `--safe --without-K`. 3d.6 + 3d.7 + 3d.8 (2026-04-29) added 4 more — 3d.6 `DBC/TextParser/Properties/Topology/SignalList.agda`; 3d.7 `DBC/TextParser/Properties/Topology/Resolve.agda`; 3d.8 `DBC/TextParser/Format/Message.agda` + `DBC/TextParser/Properties/Topology/Message.agda` — all `--safe --without-K`. 3d.5.d-BU_ (2026-04-29, `abc7d0f`) added 1 more — `DBC/TextParser/Format/Nodes.agda` — `--safe --without-K`. 3d.5.d-EV_ (2026-04-29, `21a3146`) added 1 more — `DBC/TextParser/Format/EnvVar.agda` — `--safe --without-K`.  Path A.4 (3d.4 + JSON-mirror, 2026-04-27) lifted the prior 47-module `--without-K`-only cluster to `--safe --without-K` by retyping `Identifier.name`, JSON `JString`, DBC AST text fields, and LTL signal names from `String` to `List Char`.

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

- `--safe --without-K` mandatory (header pragma + `check-invariants`); the 48-module `--without-K`-only exception under `DBC/TextParser/` is documented in the flag breakdown.
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

For history (R6–R17, Path G, Phase 5.1, Phases A/B.1/B.1.x/B.2/B.3.a-c, B.3.d pre-gate, Layers 1–2, Layer 3 commits 3a/3b/3c.0–3c.4/3d.1–3d.3) see [PROJECT_STATUS.md](PROJECT_STATUS.md). Resume notes / next-session entry point: [.session-state.md](.session-state.md).

**Current track:** Phase B.3.d — universal DBC text-parser roundtrip `∀ d → parseText (formatText d) ≡ inj₂ d`. Decomposition in [PARITY_PLAN.md §B.3.d](docs/development/PARITY_PLAN.md): (1) `List Char` substrate; (2) per-primitive parse/emit lemmas; (3) per-line-construct lemmas; (4) top-level aggregator induction.

**Status (2026-04-29):** Layers 1–2 ✅; Layer 3 through 3d.3 ✅; **3d.4 + JSON-mirror + Path A ✅ shipped 2026-04-28 (commit `320c5a9` on branch `b3d-3d4-json-detaint`)**; **3d.5.a framework core + 3d.5.b parseValueTable gate + 3d.5.c-γ.1+γ.2+γ.3+ε+ζ+η + 3d.5.d parseValueTable production migration ✅ shipped on branch `b3d-3d5-format-dsl`**; **3d.6 + 3d.7 + 3d.8 ✅ shipped 2026-04-29 (commits `89e04ee` + `42228df` + `f25ca5a` on same branch)** — full BO_ block roundtrip closes Layer 3 BO_ block; **3d.5.d-BU_ ✅ shipped 2026-04-29 (commit `abc7d0f` same branch)** — 73% strict-LOC reduction; **3d.5.d-EV_ ✅ shipped 2026-04-29 (commit `21a3146` same branch)** — 94% strict-LOC reduction.

3d.5.a (3 commits `b06cc30` + `8ca94e8` + `cc3e5de`): `DBC/TextParser/Format.agda` (~430 LOC) — single inductive `Format : Set → Set₁` with constructors `literal`/`ident`/`nat`/`stringLit`/`pair`/`iso`/`many`; derived `emit`/`parse`; universal roundtrip theorem `roundtrip : ∀ {A} (f : Format A) pos a suffix → EmitsOK f a suffix → parse f pos (emit f a ++ suffix) ≡ just (mkResult a (advancePositions pos (emit f a)) suffix)` proven by structural induction in a `mutual` block with `manyHelper-roundtrip-list` (cyclic recursion through `many`).  `EmitsOKMany` lifted to inductive data type to bypass termination quirks with `concatMap`-based `emit (many f)`.  `ParseFailsAt f suffix` user-supplied for the `[]-fails` constructor.

3d.5.b (`7ddde8b`): `DBC/TextParser/Format/ValueTable.agda` (165 file-LOC, **88 strict-code-LOC**) closes `parseValueTable-format-roundtrip : ∀ pos vt outer-suffix → parse ValueTable-format pos (emit ValueTable-format vt ++ outer-suffix) ≡ just (mkResult vt …)` via one `roundtrip ValueTable-format` call backed by `build-emits-ok`.  Universal proof, not fixtures.  Gate measurement: existing `Properties/ValueTables/ValueTable.agda` is 790 file-LOC / 613 strict-code-LOC ⇒ **86% reduction** at strict-code (target was <50/<100).  **Scope honesty:** `parse ValueTable-format` is canonical-only on whitespace; the production `parseValueTable` is more permissive.  3d.5.b validates the *framework*; **3d.5.d** is what migrates the per-construct proof tree onto the DSL and drops the canonical-vs-permissive gap.

3d.5.c-γ.1 (`a3cdd23`): `Aletheia.DBC.CanonicalReceivers` (124L) + `Aletheia.DBC.TextParser.Format.Receivers` (103L).  CanonicalReceivers record carrier (`list : List Identifier; canonical : T (isCanonicalReceiversᵇ list)`), Bool predicate, smart constructor `mkCanonicalFromList` that strips singleton-`Vector__XXX`, iso-based `canonicalReceiversFmt = iso fwd bwd fwd-bwd (pair ident (many (withPrefix (',' ∷ []) ident)))`.  Joins `IntDecRat`/`NatDecRat` from `DBC.DecRat.Refinement` as the third refinement carrier.

3d.5.c-γ.2 (`2c786ef`): AST retype `DBCSignal.receivers : List Identifier → CanonicalReceivers`, cascading the change through 13 files.  CanonicalReceivers gains `mkCanonicalFromList-list : ∀ cr → mkCanonicalFromList (CanonicalReceivers.list cr) ≡ cr` lemma + `_≟ᶜʳ_` DecEq.  Existing 3d.3 dispatcher proofs (~14 sites at 156–2225 of `TextParser/Properties/Topology/Signal.agda`) project `.list` in their `All`/`SuffixStops` preconditions; `parseReceiverList∘strip-roundtrip` API still operates on `List Identifier` (δ migrates).  JSON path now strips singleton-`Vector__XXX` via `mkCanonicalFromList`, harmonising with text path.  All bindings green: Python 760p+1s, C++ 6/6, Go ok.

3d.5.c-γ.3 (`7118382`): `Aletheia.DBC.TextParser.Format.Receivers.Roundtrip` (184 file-LOC / **86 strict-code-LOC**) closes `canonicalReceivers-roundtrip : ∀ pos cr suffix → SuffixStops isReceiverCont suffix → parse canonicalReceiversFmt pos (emit canonicalReceiversFmt cr ++ suffix) ≡ just (mkResult cr …)` via one `roundtrip canonicalReceiversFmt` call backed by `build-emits-ok`.  **Gate: 79.4% strict-code-LOC reduction** vs existing 417 strict-code-LOC in `Properties/Topology/Receivers`.  Universal proof, not fixtures.

3d.5.c-ε (`01e004f`): Topology split + production migration of `parseReceiverList` onto the DSL.  `Topology.agda` (364L) split into `Topology.Foundations` (101L, cycle-relevant: `extFlagBit`/`buildCANId`/`MuxMarker`/`parseMuxMarker`/`parseByteOrderDigit`/`parseSignFlag`) + `Topology.SignalLine` (267L, BU_/SG_/BO_ machinery + redefined `parseReceiverList = CanonicalReceivers.list <$> parse canonicalReceiversFmt`) + `Topology.agda` itself (66L) becomes a re-export facade.  5 cycle-touching importers (`Properties.Primitives`, `Attributes`, `Comments`, `Properties.Comments.Comment`, `Properties.Attributes.Assign.{Message,Rel,Signal}`) redirected to `Topology.Foundations` to break the cycle Topology→Format→Properties.Primitives→Attributes→Topology.  `Properties/Topology/Receivers.agda` shrunk 646→131 file-LOC / 417→**70 strict-code-LOC = 83% reduction**.  Pre-ε existential `(parsedRs, parse-eq, strip-eq)` collapsed to flat `parseReceiverList-roundtrip`; 28 redundant `(stripVectorPlaceholder receivers)` calls in dispatcher dropped (per `feedback_no_subsumption_asymmetry`); `step28` from `cong … strip-eq` → `refl`; `stripVectorPlaceholder` helper deleted entirely.  `isReceiverCont` re-exported from `Format.Receivers.Roundtrip` (single source of truth).  δ closed (its goal — production migration of receivers — achieved via the broader ε work).

3d.5.c-ζ (`2c95462`): Format DSL constructors needed by signalLineFmt — `decRat : Format DecRat`, `wsOpt : Format ⊤` (parser zero-or-more, canonical empty emit), `ws : Format ⊤` (parser one-or-more, canonical single-space emit).  Each ships with EmitsOK clauses + roundtrip cases delegating to existing parser-roundtrip lemmas.  Three L7/L8/L9 micro-fixtures mirror L5/L6 as drift indicators.

3d.5.c-η (`648fd0b`): production migration of `parseSignalLine` onto the Format DSL.  `Topology/SignalLine.agda` redefines `parseSignalLine = parse signalLineFmt`; the per-MuxMarker dispatcher proofs in `Properties/Topology/Signal.agda` collapse from ~1873 strict-code-LOC of step-by-step bind-chain reasoning (3d.3 era) to ~256 strict-code-LOC of slim wrappers around the universal `signalLine-roundtrip`.  **86% strict-code-LOC reduction**.  New modules: `Format/SignalLine.agda` (322 file-LOC, 6-chunk composition: `headerFmt`/`muxMarkerFmt`/`sizeFmt`/`scalingFmt`/`rangeFmt`/`tailFmt`) + `Format/SignalLine/Roundtrip.agda` (511 file-LOC, universal `signalLine-roundtrip` + `build-emits-ok` from two domain preconditions: `name-stop` + `recv-cont-stop`).  Cycle break: `RawSignal` + `mkRawSignal` moved to `Topology.Foundations` (same pattern as ε).  Format DSL extended with `wsCanonOne` (parser zero-or-more, canonical single-space emit) for the 7 production-permissive whitespace slots — distinct from ζ's `ws` (one-or-more) and `wsOpt` (canonical empty emit).  Bridge `emit-signalLineFmt-eq-emitSignalLine-chars` (DSL emit ≡ existing formatter): per-construct case-split bridges (byteOrderFmt/signFlagFmt/canonicalReceiversFmt) + `inner-bridge` (chunk-flatten via 7 ++-assoc applications across 3 seams: size 3, scaling 2, range 2) wrapped in `cong (λ x → PREFIX ++ x)`.  See `feedback_assoc_rewrite_through_with_abstraction.md` for the load-bearing pattern (++-assoc rewrite fails through stuck `with`-abstractions; explicit `flatten-4`/`flatten-2` helpers via lambda-bound prefix is the workaround).

3d.5.d (`b374217`): production migration of `parseValueTable` onto the Format DSL.  `TextParser/ValueTables.agda` redefines `parseValueTable = parse ValueTable-format >>= many parseNewline >>= pure` (3-line wrapper, mirrors η's `parseSignalLine = parse signalLineFmt` line+block split).  `Format/ValueTable.agda` extended from canonical-only (88 strict-LOC, 3d.5.b gate) to production-permissive (177 strict-LOC) via three new sugar combinators: `withWS` (canonical single-space, parser one-or-more), `withWSCanonOne` (canonical single-space, parser zero-or-more), `newlineFmt = altSum (literal "\r\n") (literal "\n")` (LF / CR-LF, canonical bare LF).  `ValueTableNameStop` precondition migrated upstream to host alongside the format.  `Properties/ValueTables/ValueTable.agda` 613 → 105 strict-code-LOC = **83% production-side reduction** (combined Format + Properties 701 → 282 = 60% combined).  Bridge `emit-ValueTable-format-eq-emitValueTable-chars` (DSL emit ≡ existing formatter): `emit-many-eq-foldr` structural induction over entries (re-associates `++` with terminator to push terminator inside recursion) + `cong (λ x → toList "VAL_TABLE_ " ++ name ++ x)`.  Slim `parseValueTable-roundtrip` via 3-step `bind-just-step` chain (parse-line success via `parseValueTable-format-roundtrip` → many-newline-exhaust → pure) + `subst` for input/output position transport.  Module count unchanged at 193 (3 files modified, no new modules).

3d.6 (`89e04ee`): `parseSignalLines-roundtrip` over `many parseSignalLine` via the framework's universal `roundtrip (many signalLineFmt)`.  New module `Properties/Topology/SignalList.agda` exposes `expectedRawOfDBC : Maybe Identifier → ℕ → DBCSignal → RawSignal`, `expectedMux`, `expectedMuxFor`, `parseSignalLines-roundtrip`, plus `SignalLineWF` per-signal precondition + `MasterCoherent` predicate.

3d.7 (`42228df`): `resolveSignalList-roundtrip` recovers `List DBCSignal` from formatter-emitted `List RawSignal` under `MasterCoherent` + per-signal `WellFormedSignal` + `PhysicallyValid` + `WellFormedTextPresence`.  New module `Properties/Topology/Resolve.agda`.  Two key insights: `findMuxName ∘ map expectedRawOfDBC ≡ findMuxMaster` under `MasterCoherent` (master agreement traverses formatter raw projection without losing identity); `buildSignal rawDlc master (expectedRawOfDBC master rawDlc s) ≡ just s` for every well-formed signal (rebuild is structurally injective on WF inputs).  Pure structural induction on `buildAllRaw` (top-level so `where`-bound names accessible).  Two `SigOK` predicates (`sigok-always` for trivial all-OK case, `sigok-when` per-signal) glue the cases.

3d.8 (`f25ca5a`): full BO_ block composer.  η-style production migration: `parseMessage = parse messageHeaderFmt >>= λ hdr → many parseSignalLine >>= λ raws → many parseNewline *> buildMessage rawId msgName rawDlc msgSender raws`.  New modules: `Format/Message.agda` (91L: `messageHeaderFmt : Format (ℕ × Identifier × ℕ × Identifier)` via inner pair tower glued with `withPrefix "BO_"` / `withWS`/`withWSOpt`/`newlineFmt` + top iso flattening 5-tuple `ℕ × (Identifier × (ℕ × (Identifier × ⊤)))` to flat) + `Properties/Topology/Message.agda` (542L: full proof tree).  **Spine-based `emitMessage-chars-decompose` (load-bearing for future BO_-style multi-line composers).**  Initial attempt was 6-deep manually-nested `trans`/`cong`; user mid-task feedback "Careful with the trans-cong piling" prompted refactor to recursive `flatten-spine : ∀ (xs : List (List Char)) (tail X : List Char) → (foldr _++ₗ_ tail xs) ++ₗ X ≡ foldr _++ₗ_ (tail ++ₗ X) xs`.  Reusable for any future `withPrefix`-glued line format.  **`messageHeader-roundtrip`** is a one-liner over `roundtrip messageHeaderFmt` + 13-slot `build-messageHeaderFmt-EmitsOK`.  **`parseMessage-roundtrip`** composes via 4 `bind-just-step` peels (header / SG_ block via 3d.6 / trailing newlines / build via local `buildMessage-roundtrip` (composes 3d.7)) wrapped in a `shape-bridge` rewriting `emitMessage-chars msg ++ outer-suffix` to `hdr-emit ++ body ++ '\n' ∷ outer-suffix`.  **Two-stage `pos-eq` (advisor-reviewed)**: (a) two `advancePositions-++` applications collapse `pos-after-nl` to structural concat form; (b) one `cong (advancePositions pos) (sym (emitMessage-chars-decompose msg))` step bridges to canonical `advancePositions pos (emitMessage-chars msg)` form so Layer 4's `parseMessages-roundtrip` doesn't need per-message position bridging.  Module count 193 → 197 (+SignalList +Resolve +Format/Message +Message Properties; all `--safe --without-K`).  `cabal run shake -- check-properties` 7m18s clean.  No semantic shift on streaming hot path — `parseMessage` and the spine machinery run only at DBC config time.

3d.5.d-EV_ (`21a3146`): production migration of `parseEnvVar` (EV_ environment-variable line) onto Format DSL.  η-style: `parseEnvVar = parse envVarFmt >>= λ ev → many parseNewline >>= λ _ → pure ev` (ValueTable wrap shape — formatter emits exactly one `\n`, captured by the DSL's `newlineFmt`; wrapper's `many parseNewline` consumes zero from outer-suffix).  New module `Format/EnvVar.agda` (404 file-LOC, 220 strict-LOC): `envVarFmt : Format EnvironmentVar` via outer iso wrapping a 22-deep nested `pair`/`withWS`/`withPrefix`/`withWSOpt`/`newlineFmt`/`discardFmt` tower covering the full EV_ wire grammar (`EV_` keyword + name + `:` + varType digit + `[` + min + `|` + max + `]` + unit-string-lit + initial + accessID + accessNode + `:` + receiverIdent + `;` + line-terminator).  **`discardFmt` sugar combinator** (parse permissively, emit canonical default): `iso (λ _ → tt) (λ _ → default) (λ _ → refl) f` — used for the 4 wire-only EV_ fields (the leading 0 / unused-int-typed slots) so the `EnvironmentVar` record carries only the 5 fields it semantically needs while the wire format preserves the 14-token cantools shape.  **`varTypeFmt` via altSum-tree + iso** (3-way ADT-valued format): `(literal '0') altSum (literal '1') altSum (literal '2')` flattened through an outer iso to `IntVar` / `FloatVar` / `StringVar`.  Public `EnvVarNameStop` precondition migrates upstream to `Format.EnvVar`; Properties re-exports for source compatibility.  Universal `parseEnvVar-format-roundtrip` one-liner over `roundtrip envVarFmt` + `build-emits-ok`.  `Properties/EnvVars/EnvVar.agda` 1,289 → 83 strict-LOC = **94% production-side reduction** (file-LOC 1,581 → 161 = 90% reduction; combined Format + Properties = 303 strict-LOC).  Bridge `emit-envVarFmt-eq-emitEnvVar-chars` via 3-case-split on `EnvironmentVar.varType ev` (IntVar / FloatVar / StringVar — all `refl` after definitional reduction; case-dependent emit doesn't propagate through the iso without the case split).  Slim `parseEnvVar-roundtrip` via 3-step `bind-just-step` chain (parse-line success via `parseEnvVar-format-roundtrip` → `manyHelper-parseNewline-exhaust` → pure) + `cong (advancePositions pos) bridge` for position transport.  **Helper-signature pattern** (recovery): initial inline `subst` blew the paren-balance count on the 22-deep nested expression; refactor extracted `ws-slot1-witness` + `emit-varTypeFmt-head-non-hspace` + `decRat-head-non-hspace` private helpers with **left-bracketed `((emit X ++ inner-rest) ++ outer-suffix)`** signatures matching Agda's natural EmitsOK reduction `emit (pair X Y) (a, b) ++ outer-suffix → (emit X a ++ emit Y b) ++ outer-suffix`.  Module count 198 → 199 (+ Format/EnvVar; `--safe --without-K`).  `cabal run shake -- check-properties` 7m27s clean.  No semantic shift on streaming hot path — `parseEnvVar` runs at DBC config time only.

3d.5.d-BU_ (`abc7d0f`): production migration of `parseBU` (BU_ node-list line) onto Format DSL.  η-style: `parseBU = parse nodeListFmt >>= λ ns → many parseNewline >>= λ _ → pure ns`.  New module `Format/Nodes.agda` (244 file-LOC, 114 strict-LOC): `nodeListFmt : Format (List Node)` via outer iso `(List Identifier × ⊤) → List Node` (forward `map mkNode ∘ proj₁`, witness `map-mkNode-Node-name : map mkNode (map Node.name ns) ≡ ns`) wrapping `withPrefix "BU_" + withWSOpt + withPrefix ":" + pair (many nodeEntry-format) (withWSOpt newlineFmt)`.  Public `nodeEntry-format = withWS ident` (mirror of public `ValueEntry-format`); public `NodeNameStop` precondition + universal `parseNodeList-format-roundtrip` one-liner over `roundtrip nodeListFmt` + `build-emits-ok` builder.  `Properties/Topology/Nodes.agda` 439 → 117 strict-LOC = **73% production-side reduction**.  Bridge `emit-nodeListFmt-eq-emitBU-chars-prefix : emit nodeListFmt ns ++ '\n' ∷ [] ≡ emitBU-chars ns` (note displaced trailing `\n` — the formatter emits `BU_:…\n\n` while the DSL emits `BU_:…\n`; the wrapper's `many parseNewline` consumes the second `\n` plus any further blanks): `emit-many-eq-foldr` structural induction over `ns` + two `++ₗ-assoc` applications + `cong (toList "BU_:" ++ₗ_)`.  Slim `parseBU-roundtrip` via 3-step `bind-just-step` chain (shape-bridge via `++ₗ-assoc` to reshape input → parse-line success via `parseNodeList-format-roundtrip` → trailing `\n` via `many-parseNewline-one-LF-stop`) + 2-stage `pos-eq` from 3d.8 (one `advancePositions-++` + bridge cong) to collapse `pos-after-nl` to canonical `advancePositions pos (emitBU-chars ns)` form.  `NodeNameStop` precondition migrated upstream to `Format.Nodes`; Properties re-exports for source compatibility.  Module count 197 → 198 (+ Format/Nodes; `--safe --without-K`).  `cabal run shake -- check-properties` 7m37s clean.  No semantic shift on streaming hot path — `parseBU` runs at DBC config time only.

3d.4 + JSON-mirror + Path A details: single mega-commit (98 files, +1545/-1314).  Module-flag invariants post-3d.5.d-EV_: **199 modules total** (was 198 post-3d.5.d-BU_; +1 new for Format/EnvVar, `--safe --without-K`); 194 `--safe --without-K` + 4 `--safe --no-main` + 1 `--without-K`-only (Substrate.Unsafe).  Stream LTL +12-38% across bindings (Path A.5 Bool fast path); Signal Extraction -2-9% / Frame Building -1-7% (Path A structural cost; γ.2 incremental cost folds into the Path A profile, no fresh regression beyond what 320c5a9 already accepted; ε/ζ/η/3d.5.d/3d.6/3d.7/3d.8/3d.5.d-BU_/3d.5.d-EV_ are proof-only and runtime-neutral on the streaming hot path — `parseSignalLine`, `parseValueTable`, `parseMessage`, `parseBU`, and `parseEnvVar` all run at DBC config time only).  Baselines NOT refreshed per user "wait and see" 2026-04-28; COMPILE-pragma escape hatch deferred (now requires explicit user approval per `feedback_no_suppression_without_approval`).  Per-commit detail in PROJECT_STATUS.md and `memory/project_b3d_universal_proof.md`.

**Architectural plan locked 2026-04-26 (post-3d.3b) + amended 2026-04-27 (JSON-mirror addition)** per [PARITY_PLAN.md §B.3.d](docs/development/PARITY_PLAN.md):
1. **3d.4 + JSON-mirror + Path A ✅ shipped 2026-04-28** (commit `320c5a9`).  See above.
2. **3d.5 Format DSL framework (~4–6w):** sub-phases (a) framework core ✅; (b) single-construct validation gate (parseValueTable canonical-only, 88 strict-LOC) ✅; (c) pinch-point extensions ✅ — α `refined` constructor ✅, β `altSum` + `withPrefix` ✅, γ.1 `CanonicalReceivers` refinement carrier ✅, γ.2 AST retype + cascade ✅, γ.3 receivers DSL roundtrip ✅, ε Topology split + parseReceiverList DSL migration ✅ (δ subsumed), ζ Format DSL +decRat/wsOpt/ws ✅, η parseSignalLine DSL migration + Format/SignalLine + bridge + 86% reduction ✅; **(d) migration of remaining 3a–3d.3 proofs onto DSL (~2-3w) — IN PROGRESS:** parseValueTable ✅ shipped 2026-04-28 (`b374217`, 83% production-side reduction, +permissive-whitespace `withWS`/`withWSCanonOne`/`newlineFmt` sugar); BU_ ✅ shipped 2026-04-29 (`abc7d0f`, 73% production-side reduction); 3a (Preamble) + 3b EV_/CM_ + 3c (BA_DEF_ family) pending.  **(e) apply to renumbered 3d.6–3d.8 ✅ shipped 2026-04-29 (commits `89e04ee` + `42228df` + `f25ca5a`)** — full BO_ block roundtrip closes Layer 3 BO_ block.  (f) Layer 4 aggregation (~3-5d).

**Layer 3 status post-3d.5.d-EV_**: BO_ block ✅ closed; ValueTable ✅; BU_ ✅; EV_ ✅.  Remaining pending: 3d.5.d migrations of 3a (Preamble) + 3b (CM_ — heaviest at 2,533L) + 3c (BA_DEF_ family) onto DSL → Layer 4 (parseDBC aggregator).

**Layer 4 pending**: top-level aggregator induction over `DBC` (becomes `roundtrip DBC-format` once DSL lands) + char-class-disjointness bridge lemmas (`isIdentStart→¬isHSpace`, `isIdentCont→¬isHSpace`, `isIdentCont→¬isNewlineStart`) + `showInt-chars-head-non-hspace` (~15L, locally provable).

**Cross-binding parity roadmap**: [docs/development/PARITY_PLAN.md](docs/development/PARITY_PLAN.md), locked after R17. Active deferrals (R17-DEF-1..6, B.3.d Layer 4 owed lemmas, B.3.d-gated cantools drop) tracked in `memory/project_*.md`.
