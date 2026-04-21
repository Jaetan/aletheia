# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). The core logic is implemented in Agda with correctness proofs, compiled to Haskell, and exposed through Python, C++, and Go APIs.

**Current Phase**: See [PROJECT_STATUS.md](PROJECT_STATUS.md) for detailed phase status

## Table of Contents

- [Global Project Rules](#global-project-rules)
- [Common Commands](#common-commands)
- [Architecture](#architecture-three-layer-design)
- [Module Structure](#module-structure)
- [Development Workflow](#development-workflow)
- [Key Files](#key-files)
- [Requirements](#requirements)
- [Important Notes](#important-notes)
- [Troubleshooting](#troubleshooting)
- [Performance Considerations](#performance-considerations)
- [Implementation Phases](#implementation-phases)
- [Current Session Progress](#current-session-progress)

## Development Environment

**IMPORTANT: These facts must be preserved across session compression.**

- **Agda binary**: `/home/nicolas/.cabal/bin/agda`
- **Shell**: `/usr/bin/fish`
- **Shell config**: Source `/home/nicolas/.config/fish/config.fish` when needed
- **User binaries**: `/home/nicolas/.local/bin` (accessible)
- **User libraries**: `/home/nicolas/.local/lib` (accessible)

**Type-checking command**:
```bash
/home/nicolas/.cabal/bin/agda +RTS -N32 -RTS /home/nicolas/dev/agda/aletheia/src/Aletheia/YourModule.agda
```

## Global Project Rules

### AGENTS.md as Coding Standards

[AGENTS.md](AGENTS.md) defines per-language categories, guidelines, and verification commands. **Follow these as coding standards when writing code, not only as review checklists.** Before writing or modifying code in any language, consult the relevant language section in AGENTS.md and produce code that already conforms to its categories and guidelines.

### Agda Module Requirements (MANDATORY)

**Every Agda module MUST use**:
```agda
{-# OPTIONS --safe --without-K #-}
```

**Rationale**:
- `--safe`: Prohibits postulates, unsafe primitives, and non-terminating recursion
  - Ensures all code is fully verified or uses runtime checks
  - Prevents accidental holes in production logic
  - Forces explicit documentation of any assumed properties
- `--without-K`: Ensures compatibility with Homotopy Type Theory (HoTT)
  - Makes proofs more general and reusable
  - Required for certain classes of formal verification

**Library-level flag** (set in `aletheia.agda-lib`, applies to all modules):
- `--erasure`: Enables the `@0` (erased) modality for zero-cost type-level information
  - Used for phantom type parameters (e.g., `Timestamp μs` where `μs` is erased)
  - Erased arguments are removed at compile time — no runtime overhead
  - This flag is in the library file, not per-module OPTIONS pragmas

**Exceptions**:
- If postulate is truly needed (rare), create separate `*.Unsafe.agda` module
  - Remove `--safe` flag ONLY in that module
  - Document why postulate is needed
  - Must be replaced with proof before production use

**Enforcement**:
- Build system checks all modules have --safe flag
- CI/CD should verify no unsafe modules in production paths
- Code review checklist includes verifying flags

**Current Status**: ✅ All 143 Agda modules use `--safe --without-K`

### Module Safety Flag Breakdown

**By flag combination** (143 total):
- **139 modules**: `--safe --without-K` (standard safe modules)
- **4 modules**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)

**All 143 modules use `--safe`**. No modules require `--sized-types`.

## Common Commands

See [Building Guide](docs/development/BUILDING.md) for comprehensive build instructions, including:
- Build system commands (Shake via Cabal)
- Python virtual environment setup
- Common development workflows
- Troubleshooting build issues

Quick reference for development:
```bash
# Type-check a single Agda module
cd src && agda +RTS -N32 -RTS Aletheia/YourModule.agda

# Build everything
cabal run shake -- build

# Run Python tests
cd python && python3 -m pytest tests/ -v

# Run type checking (MUST run from python/ directory)
cd python && basedpyright aletheia/

# Run linting (MUST run from python/ directory)
cd python && pylint aletheia/

# Build and test C++ binding
cd cpp && cmake -B build && cmake --build build && ctest --test-dir build

# Run cross-language benchmarks (requires all bindings built)
bash benchmarks/run_all.sh --frames 1000 --runs 5 --bench throughput
```

## Architecture (Three-Layer Design)

See [Architecture Overview](docs/architecture/DESIGN.md) for the three-layer design and critical design principle.

## Module Structure

Agda modules are organized by package. See [README.md](README.md#project-structure) for the complete file tree.

Core packages:
- **Parser/**: Parser combinators and string utilities
- **CAN/**: CAN frame encoding/decoding
- **DBC/**: DBC file parser
- **LTL/**: Linear Temporal Logic (Syntax, Incremental, Semantics, Adequacy, Coalgebra, SignalPredicate, SimplifySound, Reachable, JSON)
- **Trace/**: Trace types and streaming
- **Protocol/**: JSON protocol and streaming state machine

## Development Workflow

### Adding New Features

1. **Design in Agda**: Define types and properties in appropriate module
2. **Implement with proofs**: Write code and prove correctness
3. **Build and test**: `cabal run shake -- build` then test shared library
4. **Update language bindings** (if needed): Add convenience functions
5. **Add examples**: Create test cases in `examples/`

### Typical Iteration Cycle

```bash
# 1. Edit Agda source
vim src/Aletheia/Parser/Combinators.agda

# 2. Quick type-check (fast feedback, no compilation)
cd src && agda +RTS -N32 -RTS Aletheia/Parser/Combinators.agda

# 3. Full build when ready (also builds FFI shared library)
cd .. && cabal run shake -- build

# 4. Run Python tests
cd python && python3 -m pytest tests/ -v
```

### Incremental Builds

Shake tracks dependencies automatically. After modifying an Agda file, only affected modules are recompiled. First full build takes ~60s (stdlib ~20s + project modules), but subsequent builds are much faster (~5-15s for changes).

## Key Files

- **aletheia.agda-lib**: Agda library configuration (see the file itself for the pinned stdlib version)
- **Shakefile.hs**: Custom build system orchestrating Agda → Haskell → shared library
- **haskell-shim/aletheia.cabal**: Haskell package definition (includes `foreign-library aletheia-ffi`)
- **haskell-shim/src/AletheiaFFI.hs**: FFI exports (Python ctypes, C++ and Go dlopen)
- **python/pyproject.toml**: Python package configuration
- **cpp/CMakeLists.txt**: C++23 binding build (CMake 3.25+, FetchContent for nlohmann/json + Catch2)
- **docs/FEATURE_MATRIX.yaml**: Authoritative cross-binding feature parity matrix; paired structural gate tests in `python/tests/`, `go/aletheia/`, `cpp/tests/` fail CI on silent symbol removal. See `docs/development/PARITY_PLAN.md` for the roadmap.

## Requirements

See [Building Guide](docs/development/BUILDING.md#prerequisites) for detailed requirements and installation instructions.

## Important Notes

### Agda Compilation

- Always use `--safe --without-K` flags (enforced in module headers)
- Four modules use `--no-main` (see Module Safety Flag Breakdown above)
- Generated MAlonzo code goes to `build/` directory
- Don't edit generated Haskell code; modify Agda source instead
- **Performance**: Use parallel GHC with `agda +RTS -N32 -RTS` for all modules
  - Critical for Protocol/StreamState.agda and Main.agda (17s vs >120s timeout)
  - Recommended for all type-checking to maximize performance
- **First build**: Standard library compiles on first `agda` invocation (~20s one-time cost, cached thereafter)

### MAlonzo FFI and Name Mangling

MAlonzo mangles function names (e.g., `processJSONLine` → `d_processJSONLine_4`). The build system auto-detects mismatches and provides exact fix commands:

```bash
cabal run shake -- build
# If mismatch: ERROR with sed command to fix it
```

**When it triggers**: Rarely - only when adding/removing Agda definitions before `processJSONLine` in Main.agda.

**Best Practice**: Keep `AletheiaFFI.hs` minimal, update mangled names when needed. Alternative solutions (COMPILE pragmas) would compromise `--safe` guarantees.

### Virtual Environment

See [BUILDING.md](docs/development/BUILDING.md#2-set-up-python-virtual-environment) for Python virtual environment setup.

Quick reference: Create with `python3 -m venv .venv`, activate with `source .venv/bin/activate`

### C++ Binding

File/test inventory and phase deliverables live in [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics). This section covers design only.

The C++23 binding lives in `cpp/` and wraps `libaletheia-ffi.so` via `dlopen`:
- **Design**: `IBackend` interface abstracts FFI boundary; `MockBackend` replays JSON for testing; strong types everywhere (`std::byte`, validated newtypes, `std::expected`)
- **Observability**: Custom `Logger` class (`log.hpp`, ~90 lines) — callback-based structured logging with 15 event types matching Go's slog; zero-cost when null (default)
- **RTS cores**: `make_ffi_backend(path, rts_cores)` — default 1; once-per-process with mismatch warning
- **Build**: `cd cpp && cmake -B build && cmake --build build && ctest --test-dir build`
- **Style**: `.clang-format` + `.clang-tidy` enforce naming/formatting; C++23, targets g++>=14 and clang>=21

### Go Binding

File/test inventory lives in [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics). This section covers design only.

The Go binding lives in `go/` and wraps `libaletheia-ffi.so` via cgo + dlopen:
- **Optional Excel package**: `go/excel/` is a separate Go module (separate `go.mod`) that pulls in the heavy `xuri/excelize` dependency chain; depend on it only if you need the Excel loader.
- **Design**: `Backend` interface abstracts FFI; `MockBackend` replays JSON for testing; `FFIBackend` loads .so via `dlopen`/`dlsym` with C trampolines; strong types (`[]byte` payload with DLC-based validation, validated newtypes for CAN ID / DLC, sealed interfaces for CanID/Predicate/Formula)
- **Observability**: `slog` structured logging via `WithLogger` option (15 event types); `ViolationEnrichment.CoreReason` carries Agda core reason strings
- **RTS cores**: `NewFFIBackend(path, WithRTSCores(n))` — functional option, once-per-process with mismatch warning
- **Concurrency**: `Client` is goroutine-safe (`sync.Mutex`), double-close safe, GHC RTS init thread-pinned (`LockOSThread`)
- **Build/test**: `cd go && go test ./aletheia/ -v -count=1 -race`
- **Style**: `gofmt` + `go vet` clean; godoc on all exports

### Haskell FFI Layer

The Haskell FFI layer is split across 3 files (~470 lines total):
- **AletheiaFFI.hs** (~277 lines): `foreign export ccall` wrappers → `libaletheia-ffi.so`
- **AletheiaFFI/Marshal.hs** (~95 lines): Agda type construction helpers (AgdaFrame, AgdaTime, etc.)
- **AletheiaFFI/BinaryOutput.hs** (~99 lines): Binary response encoding helpers

**Design**:
- AletheiaFFI.hs wraps `processJSONLine` (JSON commands) and `processFrameDirect` (binary data frames via `aletheia_send_frame`) with C-callable exports
- State managed via `StablePtr (IORef StreamState)`
- All bindings load the `.so` via ctypes/dlopen — no subprocess overhead
- Never add business logic here

### Module Organization

When adding new Agda modules:
- Follow existing package structure (Parser, CAN, DBC, LTL, etc.)
- Include correctness properties alongside implementations
- Use descriptive module names (e.g., `Properties.agda` for proofs)
- Update Main.agda if new functionality needs exposure

### Import Naming Conventions

When importing stdlib modules with conflicting names, use **subscript suffix** pattern for consistency:

**Standard naming:**
- String operators: `_++ₛ_`, `_≟ₛ_`
- List operators: `_++ₗ_`
- Rational operators: `_+ᵣ_`, `_*ᵣ_`, `_-ᵣ_`, `_≤ᵣ_`

**Example:**
```agda
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.Rational using () renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_)

-- Usage (underscores invisible at call sites)
result = "hello" ++ₛ "world"   -- NOT _++ₛ_
combined = list1 ++ₗ list2
```

**Important**: Underscores are invisible in infix usage, but remain when passing operators as parameters (e.g., `foldr _++ₛ_ ""`).

## Troubleshooting

_Build-time issues beyond this table are collected in [BUILDING.md § Troubleshooting](docs/development/BUILDING.md#troubleshooting)._

**Build failures**: `cabal run shake -- clean && cabal run shake -- build`

**Python issues**: Verify venv active (`which python3` → should show `.../.venv/bin/python3`)

**Agda module not found**: Check `~/.agda/libraries` lists standard-library path and `~/.agda/defaults` contains "standard-library"

**MAlonzo name mismatch**: Build provides exact sed command - just run it

**Type-checking timeout**: Always use `agda +RTS -N32 -RTS` for parallel GHC

**`hs_init` failure at first client start**: Symptom is `aletheia_init() returned null` from Python/C++/Go. Usually means the `.so` was built against a different GHC runtime than what's present at load time. Rebuild the shared library (`cabal run shake -- build` — the Shakefile rebuilds `libaletheia-ffi.so`) and make sure no stale copy is shadowing it in `$LD_LIBRARY_PATH`.

**`.so` load failure (`OSError: cannot open shared object file`)**: The FFI loader looks at `_install_config.LIBRARY_PATH` first, then `LD_LIBRARY_PATH`, then `/usr/local/lib`. If you moved the shared library, regenerate `_install_config.py` via `cabal run shake -- install` or point `ALETHEIA_FFI_PATH` at the new location.

**ctypes signature mismatch (Python)**: Symptoms are segfaults, garbage return codes, or `TypeError` on the first FFI call. Usually means `libaletheia-ffi.so` and `aletheia` package versions have drifted. Confirm both were built from the same commit (`python -m aletheia --version`, `strings libaletheia-ffi.so | grep aletheia-ffi-`), and reinstall the Python package if they differ.

**DBC validation rejects a seemingly valid message**: Check the `ValidationIssue.code` enum — common culprits are `signal_overlaps_another`, `signal_exceeds_message_size`, and `multiplexor_value_conflict`. The human-readable table is in [PROTOCOL.md § Common Error Codes](docs/architecture/PROTOCOL.md#common-error-codes). Run `aletheia validate --dbc <file>` to see every issue, not just the first.

**Property formula parse error**: The JSON schema is strict — `"operator"` must be the exact lowercase tag and predicates must live under `{"operator": "atomic", "predicate": {...}}`. If you hand-wrote a formula, compare against `Signal("X").equals(1).to_dict()` output.

## Performance Considerations

**Parser Combinators**: Use structural recursion on input length (not fuel-based) to avoid type-checking timeouts. Helper functions avoid `with` patterns in type signatures.

**Type-Checking**: **Always use `agda +RTS -N32 -RTS`** for parallel GHC (17s vs >120s timeout for StreamState/Main). First build caches stdlib (~20s).

## Implementation Phases

See [PROJECT_STATUS.md](PROJECT_STATUS.md) for detailed phase status, deliverables, and roadmap.

**Current**: Phase 5.1 complete. Binary FFI (4.3x CAN 2.0B, 9.1x CAN-FD), CAN-FD, C++/Go bindings, cross-language benchmarks all complete. Four-tier check interface with full cross-language parity. See PROJECT_STATUS.md for detailed metrics and review history.

---

## For Human Developers

This section provides guidance for developers new to Agda or the Aletheia codebase.

**New to the project?** Start with the [Project Pitch](docs/PITCH.md) to understand why Aletheia exists and what it solves.

### For Agda Newcomers

If you're new to Agda but familiar with Python/typed languages:

**Basic Syntax:**
- `→` means function arrow (like `->` in types)
- `∀` means "for all" (universal quantification)
- `ℕ` is natural numbers (type Nat with `\bN`)
- `ℚ` is rationals (type with `\bQ`)
- `≡` is propositional equality (type with `\==`)

**Safety Flags:**
- `--safe` ensures no undefined behavior (like Rust's borrow checker)
  - No postulates, no unsafe primitives, all functions terminate
  - Used in all 143 Aletheia modules
- `--without-K` disables Streicher's K axiom (uniqueness of identity proofs)
  - Makes code compatible with Homotopy Type Theory
  - Required for formal verification

**Dependent Types:**
Types can depend on values:
- `Vec Byte 8` - vector of exactly 8 bytes (length in type!)
- `Fin n` - numbers 0 to n-1 (bounds checking at compile time)
- `CANId` uses `ℕ` (natural numbers) with range checked at parse time

**Common Patterns:**
- **Pattern matching with `with`**: Extract intermediate values
- **Structural recursion**: Functions recurse on structurally smaller inputs
  - Parser combinators recurse on `length input` (always decreasing)
  - No fuel needed - termination guaranteed!
- **Module imports with renaming**: Avoid name clashes (see Import Naming Conventions above)

**Reading Error Messages:**
- **Yellow highlighting**: Type mismatch - check expected vs actual types
- **"Not in scope"**: Import missing or wrong module name
- **"Termination checking failed"**: Function might not terminate
  - Use structural recursion on input length or add fuel parameter
  - See Parser/Combinators.agda for examples
- **"_X_42 is not defined"**: Agda generates metavariables - fill the hole!

**Why formal methods for automotive?**
- Guarantees correctness (not just testing)
- Signal extraction bugs can cause safety issues
- LTL properties prove temporal safety constraints

**Key terms used elsewhere in this file:**
- **MAlonzo**: Agda's Haskell backend. `agda --compile` produces a `MAlonzo/` directory of generated `.hs` files; the Cabal package and FFI shared library are built on top of those. Function names get mangled (e.g., `processJSONLine` → `d_processJSONLine_4`).
- **stdlib / agda-stdlib**: The Agda standard library (`agda-stdlib`). Pinned to v2.3 in `aletheia.agda-lib`. Provides `Data.Nat`, `Data.List`, `Relation.Binary.PropositionalEquality`, etc.
- **HoTT (Homotopy Type Theory)**: A foundational framework where types correspond to topological spaces and equalities are paths. `--without-K` makes the codebase compatible with HoTT-style reasoning by forbidding the K axiom (uniqueness of identity proofs).
- **`Dec A`**: A type expressing decidability: `Dec A = yes (a : A) ⊎ no (¬ A)`. Carries a *proof object* at runtime, which is why `Dec`-valued predicates allocate per call on hot paths — see "Common newcomer mistakes" below for the `Bool` workaround.
- **Kleene three-valued logic**: A logic with three truth values — true, false, and unknown — used for `FinalVerdict` (`Holds`, `Violated`, `Unsure`) when streaming truncates before a liveness property resolves.
- **`@0` / erased modality**: Enabled by the library-level `--erasure` flag. Arguments marked `@0` are erased at compile time (zero runtime cost), used for phantom type parameters like `Timestamp μs`.
- **`hs_init`**: GHC RTS startup function. The FFI shared library calls it once at first client construction; failures usually mean the `.so` was built against a different GHC than is loaded at runtime.

**Resources:**
- [Agda Documentation](https://agda.readthedocs.io/)
- [Standard Library](https://agda.github.io/agda-stdlib/)
- [Agda Tutorial](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html)

### Common newcomer mistakes

Concrete failure modes the first-time Aletheia contributor tends to hit, and the one-line fix for each:

- **Forgetting `--safe --without-K` on a new module**. The top-of-file pragma is enforced by the build system — a new module without it breaks CI. Copy the header from a neighbour.
- **Using `with x` where the proof needs to remember what `x` was**. The bare `with` form drops the equation; use `with x in eq` so you can `rewrite eq` (or `subst`) in the branches. Symptom: you can prove the goal in a hole but Agda won't accept the refined LHS.
- **Using `Dec`-valued predicates on the streaming hot path**. MAlonzo allocates a proof term per call for `Dec`; replace with a `Bool`-valued fast path plus an equivalence lemma. Missing this is what caused the R12 bench regression — see `extractSignalCoreFast` for the pattern.
- **Editing generated MAlonzo Haskell in `build/`**. The `build/` tree is overwritten on every build; changes must land in the Agda source. If you see a name-mangling mismatch, update `haskell-shim/src/AletheiaFFI.hs` using the exact `sed` command the build emits — don't edit the generated file.
- **Writing Agda parser combinators that recurse on "fuel" instead of decreasing input length**. Structural recursion on `length input` is what keeps the termination checker happy and the typechecker fast; see `Parser/Combinators.agda`. A fuel argument will either fail termination or blow up typechecking time.
- **Type-checking without `+RTS -N32 -RTS`**. Large modules (`Protocol/StreamState.agda`, `Main.agda`) time out past 120s without parallel GHC. Always use `agda +RTS -N32 -RTS`.
- **Running `pytest` / `basedpyright` / `pylint` from the repo root instead of `python/`**. The tools pick up config from the nearest `pyproject.toml`; outside `python/` they either find no tests or the wrong rules. `cd python && ...` before running any of them.

### Code Style

**Agda:**
- Naming: Follow stdlib conventions
- Indentation: 2 spaces
- Line length: Aim for 80 characters, max 100

**Haskell:**
- Style: Follow standard Haskell style
- Keep it minimal: Haskell shim should stay minimal (see Haskell FFI Layer section above)

**C++:**
- Standard: C++23, targets g++>=14 and clang>=21
- Style: `.clang-format` and `.clang-tidy` in `cpp/`
- Use `#pragma once` (not `#ifndef` guards)

**Go:**
- Style: `gofmt` (non-negotiable), `go vet` clean
- Godoc: One-line comment on all exported types, functions, constants
- Naming: Go MixedCaps, keep `CanID`/`Dbc` prefix for readability (deliberate acronym casing choice)
- Tests: `cd go && go test ./aletheia/ -v -count=1 -race`

**Python:**
- Style: PEP 8
- Type hints: Use throughout
- Docstrings: Google style

### Contributing

**Commit Messages:**
Follow conventional commits:
```
feat(CAN): Add multiplexed signal support
fix(Parser): Handle trailing whitespace in DBC
docs(BUILDING): Add macOS-specific notes
```

**Before Committing:**

The minimal pre-commit check (sufficient for documentation-only changes):

1. Ensure code type-checks: `agda +RTS -N32 -RTS src/Aletheia/Main.agda`
2. Build succeeds: `cabal run shake -- build`
3. Tests pass:
   - Python: `cd python && python3 -m pytest tests/ -v`
   - C++: `cd cpp && cmake -B build && cmake --build build && ctest --test-dir build`
   - Go: `cd go && go test ./aletheia/ -v -count=1 -race`

For code changes, [AGENTS.md § Step 4: Implement and verify](AGENTS.md#step-4-implement-and-verify) defines the **canonical 4-gate verification sequence** (Agda build → unit tests → lint gates → benchmarks) — that is the authoritative source. The 3-step list above is a doc-only shortcut; do not let it drift from AGENTS.md.

---

## Current Session Progress

See [PROJECT_STATUS.md](PROJECT_STATUS.md) for phase status and deliverables.

See [.session-state.md](.session-state.md) for session recovery, next steps, and current work context.

**Latest (2026-04-21):** Phase A (feature matrix + structural gates) + Phase B.1 (DBC metadata Tier 1) + Phase B.1.x (DBC metadata Tier 2 + signal receivers + message senders) + Phase B.2 (mux query helpers — closed via audit) + **Phase B.3.a → B.3.c (DBC text parser corpus + Agda skeletons + incremental construct implementation)** landed, plus pylint-gate hardening, `check-properties` Shake wiring, and three WF proof-completeness fixes ahead of B.3.d. **B.3.d in_progress**: target is the universal `∀ d → parseText (formatText d) ≡ inj₂ d` (a corpus-shape / per-fixture attempt was reverted — see PARITY_PLAN.md §B.3.d for the four-layer decomposition). Work follows the [cross-binding parity roadmap](docs/development/PARITY_PLAN.md) locked after R17.

- **Phase A** (commits `8b58ff0` → `b5bfbeb`): `docs/FEATURE_MATRIX.yaml` is now the authoritative source for cross-binding parity (29 rows × 3 bindings, grown to 35 rows after B.1.x + B.2). Structural gate tests mirror it in all three languages — Python (`tests/test_feature_matrix_parity.py`, `importlib` + `getattr`), Go (`feature_matrix_test.go`, `go/ast` source parse), C++ (`feature_matrix_tests`, `yaml-cpp` with lexical-noise strip). Any `implemented` entry that can't be resolved to a real public symbol fails CI.
- **Phase B.1** (commits `2928f63` Python, `1cc3250` C++, `e458a3a` Go + fixup `ffd8679`, `75a728c` matrix row): DBC metadata **Tier 1** — `signalGroups`, `environmentVars`, `valueTables` — widened through `dbc_to_json` and the three `DbcDefinition` structs. Tier 1 fields already existed in the Agda core and flowed through the formatter; B.1 just stopped the FFI boundary from dropping them.
- **Phase B.1.x Commit 1** (`2367812`, 37 files, +4439/−51): DBC metadata **Tier 2** — nodes (`BU_`), comments (`CM_`), and attribute definitions/defaults/assignments (`BA_DEF_`/`BA_DEF_DEF_`/`BA_`/`BA_REL_`). End-to-end wiring: Agda core types + `JSONParser` + `Formatter` (with roundtrip proofs closed in `Formatter/Properties.agda`, `MessageRoundtrip.agda`, `SignalRoundtrip.agda`), validator, and all three binding structs. `Float` bounds round-trip as exact `Rational` (`Fraction` in Python), matching R14-A7 precision handling. Matrix split: `dbc_metadata_full` stub replaced with `dbc_metadata_tier2` (implemented) + `dbc_signal_receivers` (planned, for Commit 2).
- **Phase B.1.x Commit 2** (`93c02bf`, 26 files, +534/−76): `DBCSignal.receivers : List String` (the trailing node list on `SG_` lines) + CHECK 21 `UnknownSignalReceiver` warning via `liftPerSignal`. `DBCMessage.receivers` is derived binding-side as the union of signal receivers. `Vector__XXX` cantools placeholder stripped on parse and re-emitted as fallback when the per-signal list is empty (cantools parity). New `"receivers"` JSON wire key serialized on every signal. Matrix: `dbc_signal_receivers` flipped to `implemented`; new `dbc_message_senders` row reserved for Commit 3 (`BO_TX_BU_` transmitters). Includes an R14-leftover `gofmt` fix in `go/benchmarks/main.go` (struct-tag alignment in `jsonOutput`), scope-flagged in the commit body per the "never dismiss tool gate findings as pre-existing" rule.
- **Phase B.1.x Commit 3** (`fc4242f`, 27 files, +438/−76): `DBCMessage.senders : List String` — the `BO_TX_BU_` additional-transmitter list on `BO_` lines (primary `sender : String` stays separate per Q1 option A). `dbc_to_json` splits cantools' merged `message.senders` at index 0 / 1: (primary + additional). New **CHECK 22 `UnknownAdditionalSender`** warning via `liftPerMessage`, reusing the existing `UnknownMessageSender` issue code with an "additional sender" disambiguation in the message text (Q2 yes). Completeness proof extended. New `"senders"` JSON wire key serialized on every message. Matrix: `dbc_message_senders` flipped to `implemented` × 3. `go/benchmarks/main.go` and `go/excel/excel.go` updated for the widened `NewDbcMessage` signature (mandatory caller updates, scope-flagged in the commit body).
- **Pylint gate hardening** (`c4bda3f`, 1 file, +8/0): `pythonpath = ["."]` added to `[tool.pylint.main]` so `pylint tests/` resolves `aletheia.*` without requiring editable install. Canonical dev flow is still `pip install -e .[dev]` inside `python/.venv`; this entry keeps the gate green when pylint is invoked outside the venv. Inline comment flags the pylint 4.x `source-roots` rename (semantic divergence from pylint 3's `pythonpath`) for the eventual upper-bound bump.
- **Phase B.2 (audit-only, this commit)** — Mux Query Helpers (R8). Pre-flight audit of the three bindings found the helper surface was already implemented client-side (operates on the parsed DBC value, not through JSON/FFI): Python (`dbc_queries.py`, 9 helpers re-exported at package level; 28 tests), Go (`DbcMessage.IsMultiplexed` + 8 sibling methods on `DbcMessage`/`DbcDefinition`; 27 tests), C++ (equivalent methods with lazy-index caching on name/ID lookups; 14 TEST_CASEs). Side-by-side inspection confirmed behavioral parity across all suites (empty signals, unknown multiplexor, extended-vs-standard CAN ID discrimination, lookup hit/miss). Closure: `dbc_queries_mux` matrix row flipped `planned` → `implemented` for Go with entry `DbcMessage.IsMultiplexed`; new `dbc_lookup` matrix row added (message_by_id / message_by_name / signal_by_name, all three `implemented`). PARITY_PLAN.md B.2 section rewritten with the "helpers pre-existed" audit finding and Status: ✅ Complete. Stale `project_go_features_to_explore.md` item 1 struck through. No code changes; docs + matrix only.
- **Phase B.3.a** (`4a086e8`) — DBC text parser corpus baseline. `python/tests/fixtures/dbc_corpus/` with 8 hand-authored DBCs covering every inventory row; `test_dbc_corpus_baseline.py` snapshots each through cantools' `dbc_to_json`. These snapshots are the structural done-criterion for **B.3.j cross-binding parity** (not for the Agda-side B.3.d proof, which targets the universal roundtrip theorem — see PARITY_PLAN.md §B.3.d).
- **Phase B.3.b** (`785d2cc`) — `DBC/TextParser.agda` + `DBC/TextFormatter.agda` skeletons + grammar BNF header. Properties facade placeholders split from day one per `feedback_properties_facade_split.md` — keeps the per-category sub-file structure isomorphic across parser and formatter before any proof content exists.
- **Phase B.3.c** (`441b0d2` lex → `977783f` preamble → `4fb5270` topology + `showℚ-dec` → `c6d8998` VAL_/VAL_TABLE_ → `7b55340` BA_DEF_*/BA_/BA_REL_ → `52454a0` CM_ → `f36e531` SIG_GROUP_ → `926f189` SIG_VALTYPE_ + SG_MUL_VAL_ parse-and-drop → `3399695` EV_ → `7d77dcb` top-level aggregator + `a7f255e` `showℚ-dec` denominator off-by-one fix) — 11 commits, bottom-up construct implementation ending with the `parseText` / `formatText` public entry points. Parse-and-drop constructs (SIG_VALTYPE_, multi-value SG_MUL_VAL_) have no retained Agda field; VAL_ is consumed by the parser and produced as nothing by the formatter per line 73–74 of `TextParser/Properties.agda`.
- **Pre-B.3.d infrastructure (this commit)** — `check-properties` Shake phony extended to walk `Aletheia/DBC/TextParser/Properties.agda` (currently the B.3.b skeleton — regression protection becomes live once B.3.d lemmas populate it). Plus three WF proof-completeness fixes in pre-existing proofs, surfaced by the extended walk and scope-flagged per the "never dismiss tool gate findings as pre-existing" rule:
  - **`src/Aletheia/DBC/Formatter/SignalRoundtrip.agda`** — `signal-roundtrip-LE` / `-BE` `(When mux vs)` cases used `parseNatList-roundtrip (List⁺.toList vs)`, which did not unify with the parser's `parseNatList⁺` reconstruction `n List⁺.∷ ns` (the roundtrip lemma is on `List ℕ`, not `List⁺ ℕ`). Pattern-match on `(When mux (v List⁺.∷ vs))` and combine `getNat-ℕtoJSON v | parseNatList-roundtrip vs` — `List⁺.toList (v ∷ vs)` reduces concretely to `v ∷ List⁺.toList vs`, which the existing `parseNatList-roundtrip` closes. Regression dates from B.1.x Commit 2 (`93c02bf`) when receivers normalization shifted the WF proof shape.
  - **`src/Aletheia/DBC/JSONParser/MessageWF.agda`** — `parseMessageBody-wf` and `parseMessageBody-pv` inversions were missing the `parseOptionalArray parseStringList (lookupArray "senders" obj) >>=ₑ λ senders → ...` step that B.1.x Commit 3 (`fc4242f`) added to `parseMessageBody`. Inserted the corresponding `with parseOptionalArray parseStringList (lookupArray "senders" obj) | eq₃` step between the existing `sender` and `signals` cases in both proofs, mirroring the working precedent at `JSONParser/SignalWF.agda:171` for the receivers field.
  - **`src/Aletheia/DBC/JSONParser/Properties.agda`** — `parse-wellformed` inverted only 6 of the 9 bind steps in `parseDBCWithErrors`; missing `nodes` / `comments` / `attributes` pattern-matches dated back to B.1.x Commit 1 (`2367812`). Extended the inversion chain with three additional `with parseOptionalArray parse{Node,Comment,Attribute}List (lookupArray ... obj) | eqₙ` steps before the final `refl`.
- **Phase B.3.d status** — **in_progress**. Target is the universal `∀ d → parseText (formatText d) ≡ inj₂ d` (not corpus-shape / per-fixture — an earlier attempt that proved 8 `refl`-closed point verifications on hand-crafted fixtures was reverted on 2026-04-21 because point verification is not a proof of the function-level property). Proof decomposition in PARITY_PLAN.md §B.3.d: (1) string-side substrate (`toList-++ₛ` + primitive `toList` lemmas), (2) per-primitive parse/emit lemmas, (3) per-line-construct lemmas, (4) top-level aggregator induction. Pre-implementation gate: read-only stdlib audit for the layer-1 substrate.
- **FP / DEFER:** B.1.x benchmark noise — two-batch protocol (`feedback_benchmark_noise_diagnostics.md`) confirmed apparent B1 deltas across Commits 2 and 3 were session-level WSL2/thermal noise, not real regressions. B2 (same binary, different session) normalised to within variance; cross-binding asymmetry + the new fields being parse-time-only (not per-frame hot path) sealed the diagnosis.
- **Verification:** 738 Python tests + 1 expected-skip + 111 markdown-docs fence runs; 292 C++ tests across 5 runtime ctest binaries + `static_tests`; 240 Go tests `-race` clean; **1270 total** (B.3.a added corpus baseline snapshot tests; B.3.b/c and this commit are Agda-side and do not change binding test counts). pyright `aletheia/` 0/0/0; pylint `aletheia/` / `tests/` / `conftest.py` all 10.00/10; ctest 6/6; go vet + gofmt clean on both `go/aletheia` and `go/excel` modules; clang-format + clang-tidy clean on B.1.x-touched files; Agda full build + `check-ffi-exports` / `check-stdlib-version` / `check-erasure` / **`check-properties` (now walks `DBC/TextParser/Properties.agda` skeleton and the three WF fixes above)** all green.

**Prior (2026-04-18 → 2026-04-19):** AGENTS.md review round 17 — decomposed into 7 commit phases (C1–C7). Aggregate diff `eae36aa..9355da9`: 12 commits, 111 files, +2605/−1704. Stamped `a8fc5b7`. See [PROJECT_STATUS.md § AGENTS.md review round 17](PROJECT_STATUS.md#phase-51-proof-gaps--spec-observations-) for the authoritative long-form summary.

- **C1** (`db2d90c`): Agda per-file items 1, 2, 4, 5, 6 + system items 13, 14, 15. New build guards: Shakefile phonies `check-ffi-exports` / `regen-ffi-exports` (paired with `haskell-shim/ffi-exports.snapshot`) and `check-stdlib-version`. PROTOCOL.md gained a "Streaming Semantics: Soundness vs. Completeness" section clarifying that `pipeline-adequate` is offline-conditional on `AllObserved`. Item #3 resolved in-source as `DEFER-stdlib-mandate` comments.
- **C1-fixup** (`2ba39df`): (8a) drop dead `_-_` from `Evaluation.agda`; (9b) uniform `InContext` wrapping + quoting across all 5 error ADTs; (11a) replace local `+-assoc-cancelʳ` with the stdlib lemma.
- **C2** (`998ba88`): Python non-#17 items 16, 18–28, 30, 32–34; `tests/` held at pylint 10.00/10 via four batches (mechanical, restructuring, protected-access, R0801 cross-file dedup).
- **C3** (`dca748f`): C++ items 35–40 + Go items 41, 43, 44, 45 + Go/C++ mirror of Python item 34; scoped CMake fix.
- **C3b** (`be33e26`) + benchmarks baseline (`774c6c8`): removed the JSON-output frame build/update path end-to-end — Agda (deleted `BatchFrameBuilding/Properties.agda` → 120 → 119 modules), Haskell shim, MAlonzo snapshot, C++ serializers, Go marshalers, Python ctypes + error code, docs.
- **C4** (`4b84cdf`): merged `rts.cores_mismatch` event scope into Lifecycle across Python / C++ / Go.
- **C5a** (`fd7a436`): docs sweep items 48–64 + Structured Logging SSOT.
- **C5b** (`5166b72` + shell-syntax fix `37b8dbc`): promoted BENCHMARKS.md to `docs/development/`.
- **C6** (`9355da9`): Python item #17 — repo-root `conftest.py` harness (pre-built DBC + parse_dbc'd `AletheiaClient` + `dbc_to_json` / `convert_dbc_file` / `iter_can_log` / `load_can_log` / `load_checks` / `load_checks_from_excel` / `load_dbc_from_excel` / `create_template` stubs) + `python/tests/test_doc_examples_harness.py` structural Cat 32 gate (parametrised over 11 tracked doc files, bans `python notest`). `pytest-markdown-docs>=0.9.2,<1` pinned in `dev` extras; AGENTS.md § Cat 32 description + Verification invocation; PYTHON_API/INTERFACES fence retags (`python` → `text` for pseudocode/return-value shapes; `continuation` where fences re-use the prior namespace).
- **FP (3):** #7 (binary-constructor rewrites inherently 2-step, not G-A2), #24 (runtime optional-dep extras float majors by design), #46 (15 events confirmed across all three bindings).
- **DEFER (6):** #3 (in-source `DEFER-stdlib-mandate`), #12 (FFI `unsafeCoerce`), #27 (DBC metadata), #31 (`send_frames_iter`), #38 (C++/Go DBC text), #42 (Go `context.Context`), plus **R17-DEF-6** — C++/Go doc-example harness mirror of C6. Tracked in `project_r17_post_review_followups.md`.
- **Verification:** 649 Python tests + 1 expected-skip + 103 markdown-docs fence runs, 273 C++ tests (R17 C3b removed JSON build/update cases), 223 Go tests, 1145 total. pyright `aletheia/` 0/0/0; pylint `aletheia/` / `tests/` / `conftest.py` all 10.00/10; ctest 5/5; go -race clean; Agda full build green. Benchmark audit (15 runs via two-batch protocol) confirmed no real regression vs R16 baseline; apparent B1 negatives were session-level WSL2/thermal noise, normalised by B2.

**Prior (2026-04-17):** AGENTS.md review round 16 — test split, doc SSOT, validator types. Commit `eae36aa` (37 files, +1536/−901).

- **Agda (M1):** `ValidationFailed : String → HandlerError` refactored to `ValidationFailed : List ValidationIssue → HandlerError`. Wire format unchanged (`formatHandlerError` flattens to single message string); structured info now preserved in the Agda value for future wire revisions.
- **C++ (H2/M14/M15/M16):** clang-format on 6 violating files (also picks up an R15 leftover in `cpp/benchmarks/benchmark.cpp` lines 386-389 — out of R16 scope, surfaced in the commit message for the audit trail). CMakeLists yaml-cpp C++20/C++23 conflict comment; OpenXLSX commit hash → release tag; `detail/cache_keys.hpp` off-limits documentation strengthened.
- **Go (M2):** Harmonized `rts.cores_mismatch` event scope.
- **Python (H4/M4-M5/M9/M12/M13):** **H4** `tests/test_unified_client.py` split (1171 > 1000-line cap) into core (591) + CAN-FD/mux (370) + events/RTS (223), shared `simple_dbc` fixture lifted to `conftest.py`; **M13** new `test_lazy_import_boundary.py` structurally guards the `aletheia/__init__.py` ↔ `client/_ffi.py` ↔ `_install_config.py` cycle; M4-M5 unused imports/vars + >100-char lines + check= cleanup; M9 COOKBOOK debug-violation + validation-errors recipes.
- **Docs (H1/H5/H6/H7/M6-M11/M17/L1):** H1 PROJECT_STATUS test counts refreshed (Python 624 / C++ 275 / Go 223 / total 1122); H5 CLAUDE.md historical session log stripped of stale module counts; H6/H7 COOKBOOK candump prereq + QUICKSTART version checks; M6 doc SSOT — confirmed remaining cross-doc references serve distinct purposes (rule definition vs status indicator vs review check) and don't constitute drift; M7 throughput qualifier scope labels (README + PITCH); M8 CLI mux-query example output; M10 PROTOCOL error/remote frame state machine; M11 broke this section's R15 dense paragraph into bullets; M17 INTERFACES.md "freely" vagueness sharpened + C++/Go DBC text workaround documented; L1 BUILDING.md install-version drift note.
- **Verification:** 624 Python tests, 275 C++ tests, 223 Go tests, 1122 total. pyright 0/0/0, pylint `aletheia/` 10.00, pylint test files 9.95 (only R0801 cross-file fixture similarity remains; refactoring would harm test clarity), ctest 5/5, go -race clean, Agda full build green. Benchmarks within ±10% inter-run variance of R15 baseline (steady-state noise floor ~2–4%; transient swings beyond ±10% trigger investigation, per R12 protocol that caught the −16.1% `log_event` regression).

**Prior (2026-04-17):** AGENTS.md review round 15 — cross-binding parity + strict protocol validation. Commit `2853644` (38 files, +617/−207).

- **Agda:** Error formatting (quoted signal names in `FrameError`); `WrappedParseError` → `WrappedParse` rename in `RouteError`.
- **C++ (CX1-CX10):**
  - CX3 — strict `IssueSeverity` parsing; Agda wire vocabulary is `{"error","warning"}` only, reject others as `ProtocolError`.
  - CX8 — `ErrorKind::BinaryUnsupported` sentinel for Go `ErrBinaryPathUnsupported` parity.
  - CX10 — `IBackend::rts_mismatch_info` out-of-line default for ABI stability.
  - clang-format applied to 11 touched files; 4 new unit tests incl. `MockBackend` `BinaryUnsupported` fallthrough.
- **Go (GO1/GO2/GO4/GO6/GO7/GO8):** GO1 removed `backend.warning` event (documented but never emitted; Python/C++/Go all now at 15 events); severity validation rejects unknown wire values; CX3 parity via switch default returning protocol error.
- **Python (14.4):** `validate_issue_severities` helper extracted to `_response_parsers.py`; monkeypatch-based fake-FFI test for unknown severity; `_client.py` held below 1000-line pylint cap via helper extraction + unused `ValidationIssue` import removed.
- **Docs (DO4-DO8):** DO5 — README 50s→46s (5M frames / 109,345 fps = 45.7s); DO8 — PROTOCOL.md new "Streaming Semantics: Soundness vs. Completeness" section explaining K5 limitation on Eventually/Until.
- **Benchmark Debug-build guard:** `benchmarks/run_all.sh` reads `cpp/build/CMakeCache.txt` and refuses Debug trees; `cpp/benchmarks/benchmark.cpp` adds `check_release_build()` (aborts at startup without `NDEBUG`) and exposes `build_type` in the JSON `system` block — prevents the silent −20% Signal Extraction regression seen when a cache was pinned to Debug.
- **Verification:** Test suites green; pyright 0/0/0, pylint 10.00, ctest 5/5, go -race clean, clang-format clean on R15-touched files, Agda full build green.

**Prior (2026-04-16):** AGENTS.md review round 14 — cross-binding correctness + PhysicalValue precision. Commit `a3208aa` (80 files, +934/−529). Section A HIGH (9): C++ `parse_frame_response` type check (A1), Python binary zero-denom raise (A2), `FRAME_SIGNAL_VALUE_OUT_OF_BOUNDS` error code added to C++/Go (A3), Python CLI DLC-vs-bytes CAN-FD fix (A4), Shakefile stdlib-mismatch (A5), Python enrichment zero-denom guard (A6), **C++ PhysicalValue double→Rational** across 19 files (A7 — exact precision matching Python's `Fraction`), WNext operator across 22 Agda files + all bindings (A8), evaluate-before-update formal proof (A9). Section B MEDIUM (13): Go cgo bounds checks (B1), Go mutable maps→accessor functions (B2), C++ MockBackend binary heuristic (B3), C++ symmetric validation (B4), backend.warning cross-binding vocab (B5), Python finalization parsing (B6), Agda ValidationFailed structured (B7), docs JSON→binary-FFI qualifier (B8), PROTOCOL.md unresolved status (B9), aletheia.h send_error/send_remote (B10), CLI.md mux-query (B11), test count fix (B12), Agda version + 16 log events (B13). Section C LOW (23): Go dead code + interface{}→any + naming (C1-C3), C++ SPDX headers + naming + Rational validation + unified MessageKey + MockBackend default test (C4-C8), Python immutability + naming + --version + test gaps (C9-C12), Agda dedup + patterns + combinators (C13-C17), Docs cross-ref consolidation (C18). 619 Python tests (+2), 268 C++ tests (+4), 276 Go tests, 1163 total. pyright 0/0/0, pylint 10.00, ctest 5/5, go -race clean. Benchmarks within WSL2 variance of R13.

**Prior (2026-04-16):** AGENTS.md review round 13 — docs-dominant round. Section A: count drift (PROJECT_STATUS C++ 40 files / Python 22 modules / Go 16+15 tests; CLAUDE.md C++/Go blocks demoted to cross-references with design-only prose). Section C: Python architecture (shallow-copy docstring in `client/_client.py`, lazy-import boundary in `aletheia/__init__.py`, 3-point coupling block in `dsl.py`, pyproject gate-mapping + re-evaluation trigger comments, CLI `mux-query` subcommand + 11 tests). `Predicate.next()` / `Property.next()` **kept but relocated** to end-of-class under a "Discouraged in CAN analysis" banner — user correction: "discouraged ≠ deprecated". Section D (28 items): PROTOCOL.md Common Error Codes table (50 codes, 6 domains), DESIGN.md "Why Agda/Haskell/JSON" rationale, QUICKSTART.md "Prerequisites & first build", CLAUDE.md "Common newcomer mistakes", README/PITCH qualified throughput numbers, PROJECT_STATUS Key Metrics with Measured column, INTERFACES side-by-side parity code + Structured Logging section, PYTHON_API `data` construction examples, DISTRIBUTION equivalence comments. Phase 6 added toolchain upgrade item (basedpyright / pylint upper-pin refresh). 617 Python tests (was 606, +11 from mux-query suite), pyright 0/0/0, pylint 10.00, ctest 5/5, go -race clean, Agda full build green. Benchmarks vs R12 post-fix baseline (Python Stream LTL 70,056 fps): R13 75,914 fps = **+8.4%**; no regression gate crossed. Other lanes within WSL2 variance.

**Prior (2026-04-15):** AGENTS.md review round 12 — 92 files touched in single commit. Agda AGDA-25 polymorphic `collectAtomsAcc`, Shakefile `check-erasure` phony, C++ test split (7 focused TUs + `test_helpers.hpp`), Go `go.work` + `concurrent_test.go`, Python structured `client/_log.py` + `benchmarks/_common.py` + `tests/test_error_code_sync.py`, Docs D1-D6. Commits `60661a1` (R12) + `1e40b4d` (post-bench `log_event` `isEnabledFor` fast-path fix). First-run Python Stream LTL regressed −16.1%; root-caused to `log_event` allocating unconditionally on hot path; post-fix Python Stream LTL +10.9% (63,173→70,056 fps). 606 Python tests, pyright 0/0/0, pylint 10.00, all ctest suites pass, go -race clean, Agda full build + 3 check-* phonies green.

**Prior (2026-04-15):** R11 — 6 batches (`bf238b3` + `222b662`). Stream LTL +2.4% C++ / +3.4% Go / +8.9% Python vs 2026-04-11 baseline.

**Prior (2026-04-14):** R10 — 68 findings: Agda (13), Go (7), C++ (12), Python (13), Docs (20). Hot-path +10.8% Stream LTL. Commit `f227d88`.

**Prior (2026-04-14):** R9 — 56 findings, commit `7203d9f`. R8 partial (`6ab5639`). Squash-merged phase-5.1→main as `a8ba94c`.

**Prior (2026-04-11):** AGENTS.md review round 7 — 51 findings across Agda (22), Go (18), C++ (9), Python (5). Commit `cdd5821`.

**Prior (2026-04-10):** AGENTS.md review round 6 — 24 findings across Agda (14), Go (4), C++ (3), Python (2). Commit `57a0358`.

**Prior (2026-04-09):** Path G — three-valued Kleene `FinalVerdict` with `Unsure` constructor.

**Prior (2026-04-08):** Closed deferred items, frame-building regression fixed.

**Prior (2026-04-07):** Phase 5.1 complete (14/14).