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

**Current Status**: ✅ All 148 Agda modules use `--safe --without-K`

### Module Safety Flag Breakdown

**By flag combination** (148 total):
- **144 modules**: `--safe --without-K` (standard safe modules)
- **4 modules**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)

**All 148 modules use `--safe`**. No modules require `--sized-types`.

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

**Latest (2026-04-24):** Phase A + B.1 + B.1.x + B.2 + B.3.a/b/c landed (2026-04-21). **Phase B.3.d pre-gate ✅ complete (2026-04-24)** — all six commits shipped (`0b7849b`, `c05083e`, `6fa29e3`, `dd9b770`, `917465b`, this commit). The pre-gate migrates every ℚ-valued DBC-on-disk field (EV_ `initial`/`minimum`/`maximum` — Commit 3/6; SG_ `factor`/`offset`/`minimum`/`maximum` — Commit 4/6; attribute `ATFloat` / `AVFloat` — Commit 5/6) to the new `DecRat` representation (`n / (2^a · 5^b)` canonical form), closing the decimal-precision gap that blocked the B.3.d universal roundtrip theorem from composing trivially.

Key artifacts:
  * `DecRat` type + canonicalisation machinery + `_≟ᵈ_` / `_≤ᵈ_` / `0ᵈ` / `1ᵈ` / `toℚ` / `fromℚ?` (Commit 1/6).
  * Universal roundtrip `fromℚ?-after-toℚ : ∀ d → fromℚ? (toℚ d) ≡ just d` (Commit 2/6 sketch → Commit 3/6 Layer-4 closure).  Four-layer proof: `stripFactor-peel` + `canonicalizeDecRat-id` + `↥/↧ₙ-toℚ-canonical` + `peel-2`/`peel-5`/`fromℚ?-raw-canonical-shape`.
  * `lookupDecRat` JSON combinator (Commit 4/6) — single `with`-step per float field in WF proofs; avoids stacked `with lookupRational ... | eq; with fromℚ? ... | eq`.
  * `toℚ` runtime optimisation via direct `mkℚ` with canonical coprime witness (Commit 4/6) — bypasses stdlib `_/_`'s gcd normalisation (which is a no-op for canonical DecRat).  Closed a 9–15% CAN-FD Signal Extraction regression AND lifted CAN 2.0B Signal Extraction **+16%** cross-binding as a bonus.  `↥-toℚ-canonical`/`↧ₙ-toℚ-canonical` simplified to `refl`/`suc-pred` as downstream benefit.
  * Option B validity predicates (DecRat-native: `factor ≢ 0ᵈ`, `minimum ≤ᵈ maximum`, `factor ≡ 1ᵈ`, `offset ≡ 0ᵈ`) with `nonZeroFactor→factorℚ≢0` bridge for the ℚ-arithmetic Encoding-layer proofs.
  * `check-properties` extended to walk `DBC/TextParser.agda` + `DBC/TextFormatter.agda` aggregators — catches the class of bug that Commit 4/6 shipped with (`RawSignal` ℚ vs DecRat mismatch in `TextParser/Topology.agda`, unreachable from Main and therefore missed by both the main build and the existing check-properties walk). Caught and fixed in Commit 5/6.
  * Cross-binding: `NonTerminatingRational "<field>"` parse error (wired in Commit 3/6) now covers EV_ + all SG_ fields + ATFloat/AVFloat.  Wire format unchanged (ℚ both directions via `toℚ`); only new failure mode is rejection of non-terminating-decimal ℚ literals.

**Next: Phase B.3.d proper.** Four-layer decomposition in PARITY_PLAN.md §B.3.d; pre-implementation gate is the layer-1 substrate decision (`project_b3d_stdlib_audit.md` Options 1–4).  User sign-off required before layer-1 code lands.

Work follows the [cross-binding parity roadmap](docs/development/PARITY_PLAN.md) locked after R17.

- **Phases A + B.1 + B.1.x + B.2 + B.3.a/b/c** — see [PROJECT_STATUS.md](PROJECT_STATUS.md) for commit SHAs and per-phase detail.  Aggregate scope: feature matrix + structural gates (Phase A); DBC metadata Tier 1/2 + signal receivers + message senders (B.1/B.1.x); mux query helpers audit-closed + dbc_lookup matrix row (B.2); DBC text parser corpus baseline + Agda skeletons + 11-commit bottom-up construct implementation (B.3.a/b/c).
- **Pre-B.3.d infrastructure** (`0035a4e`) — `check-properties` Shake phony extended to walk `Aletheia/DBC/TextParser/Properties.agda`; three WF proof-completeness fixes in `Formatter/SignalRoundtrip.agda`, `JSONParser/MessageWF.agda`, `JSONParser/Properties.agda`.
- **Phase B.3.d pre-gate — 6 commits** (`0b7849b` → `c05083e` → `6fa29e3` → `dd9b770` → `917465b` → this commit): ℚ→DecRat migration across every DBC-on-disk numeric field, closing the decimal-precision gap that blocked the universal roundtrip theorem from composing trivially.
  * **Commit 1/6** (`0b7849b`) — DecRat type, canonicalisation, `_≟ᵈ_`, `toℚ`, `fromℚ?`.
  * **Commit 2/6** (`c05083e`) — DecRat text parser (`parseDecRat`) + emitter (`showDecRat-dec`) + `fromℚ?-after-toℚ` universal sketch.
  * **Commit 3/6** (`6fa29e3`, 24 files + 2 new, +937/−116) — EV_ `EnvironmentVar.{initial,minimum,maximum}` migration; Layer-4 closure of `fromℚ?-after-toℚ` via `stripFactor-peel` + `canonicalizeDecRat-id` + `↥/↧ₙ-toℚ-canonical`; `NonTerminatingRational` parse error added cross-binding; `ErrorCode` enum extracted to `aletheia/error_codes.py`; pylint config consolidated (pyproject.toml authoritative, pylint ≥4.0 pin, `.pylintrc` deleted).
  * **Commit 4/6** (`dd9b770`, 24 files, +454/−261) — SG_ `SignalDef.{factor,offset,minimum,maximum}` migration including the hot-path Encoding.agda + Signal Extraction + 15 Agda proof files; Option B native DecRat predicates (`factor ≢ 0ᵈ`, `min ≤ᵈ max`, `factor ≡ 1ᵈ`, `offset ≡ 0ᵈ`); `nonZeroFactor→factorℚ≢0` ℚ-level bridge; `lookupDecRat` JSON combinator (single `with`-step per field in WF proofs); **`toℚ` runtime optimisation** — bypasses stdlib `_/_`'s gcd normaliser by building `mkℚ` directly with the canonical `IsCanonical→Coprime` witness.  Net benchmark result: closed the 9–15% CAN-FD Signal Extraction regression AND lifted CAN 2.0B Signal Extraction **+16.2%–+16.4%** C++/Go beyond baseline; downstream `↥/↧ₙ-toℚ-canonical` proofs simplified to `refl` / `suc-pred`.
  * **Commit 5/6** (`917465b`, 9 files, +111/−29) — Attributes `ATFloat.{min,max}` + `AVFloat.value` migration (smallest surface); `attrType-roundtrip`/`attrValue-roundtrip` close via `fromℚ?-after-toℚ` rewrites.  Scope-flagged fix for a Commit-4/6 latent bug: `RawSignal` still ℚ-typed in `TextParser/Topology.agda` (unreachable from Main's transitive closure, and therefore missed by the main build walk).  `check-properties` extended to include the `DBC/TextParser.agda` + `DBC/TextFormatter.agda` aggregator modules so the same class of gap can't recur.
  * **Commit 6/6** (this commit) — docs + memory + PARITY_PLAN.md + `.session-state.md` closing the pre-gate.
- **Phase B.3.d status** — **pre-gate ✅ complete (this commit); proof-layer work ⏳ in_progress.** Target is the universal `∀ d → parseText (formatText d) ≡ inj₂ d` (not corpus-shape / per-fixture).  Proof decomposition in PARITY_PLAN.md §B.3.d: (1) string-side substrate (`toList-++ₛ` + primitive `toList` lemmas), (2) per-primitive parse/emit lemmas, (3) per-line-construct lemmas, (4) top-level aggregator induction.  Pre-implementation gate: layer-1 stdlib audit complete 2026-04-22 — `toList-++ₛ` is only stdlib-provable via `trustMe` under `--with-K` in `Data.String.Unsafe`, so layer 1 is **not** import-and-re-export; four options in `project_b3d_stdlib_audit.md` await user decision before any layer-1 code lands.
- **FP / DEFER:** B.1.x benchmark noise — two-batch protocol (`feedback_benchmark_noise_diagnostics.md`) confirmed apparent B1 deltas across B.1.x Commits 2 and 3 were session-level WSL2/thermal noise, not real regressions.  B.3.d pre-gate Commit 4/6 initially produced a real 9–15% CAN-FD Signal Extraction regression (via per-call `toℚ` on hot path); the `mkℚ`-direct optimisation closed the regression and delivered a +16% bonus on CAN 2.0B Signal Extraction.
- **Verification:** 760 Python tests + 1 expected-skip + 111 markdown-docs fence runs (pre-gate added 4 signal-field + 3 attribute-field `NonTerminatingRational` parametrised tests vs the 753 post-B.3.c count); 293 C++ tests (+1 signal-factor integration test in Commit 4/6); 240 Go tests `-race` clean; **1293 total**.  pyright `aletheia/` 0/0/0; pylint `aletheia/` / `tests/` / `conftest.py` all 10.00/10; ctest 6/6; go vet + gofmt clean; clang-format clean on touched files; Agda full build + `check-ffi-exports` / `check-stdlib-version` / `check-erasure` / `check-properties` (now also walks `DBC/TextParser.agda` + `DBC/TextFormatter.agda` aggregators) all green.  148 Agda modules (+5 from 143 at 2026-04-21: DecRat / DecRat/RationalRoundtrip / DecRat/ScaleLemmas / TextParser/DecRatParse / TextParser/DecRatParse/Properties).

**Prior (2026-04-18 → 2026-04-19):** AGENTS.md review round 17 — decomposed into 7 commit phases (C1–C7). Aggregate diff `eae36aa..9355da9`: 12 commits, 111 files, +2605/−1704. Stamped `a8fc5b7`.

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

**Prior rounds (compressed; full detail in [PROJECT_STATUS.md](PROJECT_STATUS.md)):**

- **R16 (2026-04-17):** test split, doc SSOT, `ValidationFailed` structured. Commit `eae36aa` (37 files, +1536/−901). 1122 total tests.
- **R15 (2026-04-17):** cross-binding parity + strict protocol validation; Debug-build benchmark guard. Commit `2853644` (38 files, +617/−207).
- **R14 (2026-04-16):** cross-binding correctness + PhysicalValue precision (C++ `double` → `Rational` across 19 files, WNext operator across 22 Agda files + bindings, evaluate-before-update proof). Commit `a3208aa` (80 files, +934/−529). 1163 total tests.
- **R13 (2026-04-16):** docs-dominant round (28 doc items, count drift fixes, CLI mux-query). `Predicate.next()` relocated (not deprecated). 617 tests. Python Stream LTL 75,914 fps (+8.4% vs R12 post-fix).
- **R12 (2026-04-15):** 92-file single commit + post-bench log_event fast-path fix. Commits `60661a1` + `1e40b4d`. Python Stream LTL +10.9% after fix.
- **R11 (2026-04-15):** 6 batches (`bf238b3` + `222b662`). Stream LTL +2.4% C++ / +3.4% Go / +8.9% Python.
- **R10 (2026-04-14):** 68 findings; hot-path +10.8% Stream LTL. Commit `f227d88`.
- **R9 (2026-04-14):** 56 findings, commit `7203d9f`. R8 partial (`6ab5639`). Squash-merge `a8ba94c`.
- **R7 (2026-04-11):** 51 findings. Commit `cdd5821`.
- **R6 (2026-04-10):** 24 findings. Commit `57a0358`.
- **Path G (2026-04-09):** three-valued Kleene `FinalVerdict` with `Unsure` constructor.
- **Frame-fix (2026-04-08):** closed deferred items, frame-building regression fixed.
- **Phase 5.1 (2026-04-07):** complete (14/14).