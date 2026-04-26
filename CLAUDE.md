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

**Type-checking command** (always cap heap to prevent runaway elaboration):
```bash
/home/nicolas/.cabal/bin/agda +RTS -N32 -M16G -RTS /home/nicolas/dev/agda/aletheia/src/Aletheia/YourModule.agda
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
- `cabal run shake -- check-invariants` rejects any `^postulate` line or `Unsafe`-named module outside the allowlisted B.3.d substrate
- CI/CD runs `check-invariants` on every build
- Code review checklist includes verifying flags

**Current Status**: ✅ 135 of 168 Agda modules use `--safe`; 1 allowlisted Unsafe module (B.3.d substrate) carries the only postulates project-wide; the remaining 33 `--without-K`-only modules transitively import that substrate (32 under `DBC/TextParser/` + the allowlisted Unsafe substrate itself).

### Module Safety Flag Breakdown

**By flag combination** (168 total — `cabal run shake -- count-modules`):
- **131 modules**: `--safe --without-K` (standard safe modules; +1 from 130 post-3b: `Aletheia/DBC/DecRat/Refinement.agda` landed in 3c precursor `3a7c86e` 2026-04-25)
- **4 modules**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **33 modules**: `--without-K` only (no `--safe`) — all under `Aletheia/DBC/TextParser/`. Exactly **1** is the allowlisted Unsafe module: `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) needed to compose the B.3.d universal roundtrip theorem (mirrors stdlib's `Data.String.Unsafe`, proven by `trustMe` under `--with-K`; structurally unprovable in `--safe --without-K` because the Agda String primitives reduce only on closed terms). The other **32** transitively import that substrate via `DBC/TextParser/Lexer.agda` (which uses the bridging axioms to lift `parseIdentifier` from `List Char` to `String`); Agda's `--safe` propagation forces them to the same flag set.  Allowlisted by name in `Shakefile.hs` `check-invariants`; any other Unsafe module or `^postulate` line is rejected.

**135 of 168 modules use `--safe`**. No modules require `--sized-types`.

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
cd src && agda +RTS -N32 -M16G -RTS Aletheia/Parser/Combinators.agda

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

- Always use `--safe --without-K` flags by default (enforced in module headers); the 32-module exception under `DBC/TextParser/` is documented in the Module Safety Flag Breakdown above
- Four modules use `--no-main` (see Module Safety Flag Breakdown above)
- Generated MAlonzo code goes to `build/` directory
- Don't edit generated Haskell code; modify Agda source instead
- **Performance**: Use parallel GHC with `agda +RTS -N32 -M16G -RTS` for all modules
  - `-N32` parallelism critical for Protocol/StreamState.agda and Main.agda (17s vs >120s timeout)
  - `-M16G` heap cap prevents runaway elaboration from thrashing the host (62 GiB total + 16 GiB swap; bump only when a specific module legitimately needs it)
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

**Type-checking timeout**: Always use `agda +RTS -N32 -M16G -RTS` for parallel GHC + heap cap

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

For history (R6–R17, Path G, Phase 5.1, Phases A/B.1/B.1.x/B.2/B.3.a-c, B.3.d pre-gate) see [PROJECT_STATUS.md](PROJECT_STATUS.md). For the in-flight commit / next steps / resume notes see [.session-state.md](.session-state.md).

**Current track:** Phase B.3.d — universal DBC text-parser roundtrip `∀ d → parseText (formatText d) ≡ inj₂ d`. Decomposition in [PARITY_PLAN.md §B.3.d](docs/development/PARITY_PLAN.md): (1) `List Char` substrate; (2) per-primitive parse/emit lemmas; (3) per-line-construct lemmas; (4) top-level aggregator induction.

**Status (2026-04-26):**
- **Pre-gate ✅** (`0b7849b`–`1f175ab`, 2026-04-24): ℚ→DecRat migration across every DBC-on-disk numeric field. Universal `fromℚ?-after-toℚ` proven. `mkℚ`-direct `toℚ` runtime optimisation closed a 9–15% CAN-FD Signal Extraction regression and lifted CAN 2.0B +16% cross-binding. `NonTerminatingRational "<field>"` parse error wired cross-binding.
- **Layer 1 ✅** (`66afc2d`, 2026-04-24): 2-axiom `Properties/Substrate/Unsafe.agda` (`toList∘fromList` + `fromList∘toList`), allowlisted in `check-invariants`. Formatter refactored to `List Char` internals (`formatText = fromList ∘ formatChars`).
- **Layer 2 ✅** (`9adbc46` + `4559d5c` + `f315c6f`, 2026-04-24/25): Identifier lifted to `record { name ; valid : T (validIdentifierᵇ (toList name)) }` (5–10% Signal Extraction regression accepted; revisit angles in `project_identifier_eq_revisit.md`). `parseIdentifier-roundtrip` template + Tier A (byte-order/sign/scope/string-type) + Tier B (string-literal/mux-marker) primitives.
- **Layer 3 in_progress** — **Commit 3a `804c584` ✅** (Preamble: VERSION + BS_ + NS_; reusable Newline infrastructure under `Properties/Preamble/Newline.agda`; Properties facade pattern per `feedback_properties_facade_split.md`).  **Commit 3b `ad111bf` ✅** (Option C-broad): all four simple-line constructs land together — `BU_` (Topology/Nodes) + `VAL_TABLE_` (ValueTables/ValueTable) + `EV_` (EnvVars/EnvVar) + `CM_` (Comments/Comment) with full per-construct roundtrips wired through facade modules under `Properties/{Topology,ValueTables,EnvVars,Comments}.agda`.  CM_ proof closes the most complex Layer-3 construct: 5-way `CommentTarget` dispatch via 4-fold `<|>`-chain plus outer `pure CTNetwork` fall-through.  Heap blowup root-caused and fixed: `buildCANId-rawCanIdℕ`'s Extended clause `rewrite n+ext∸ext≡n` over a goal containing nested `ifᵀ`s replaced with pointwise `subst`; type-checks at `-M16G` (was failing at `-M48G`).
- **Layer 3 Commit 3c precursors ✅** (2026-04-25): three commits unifying every DBC numeric slot to DecRat ahead of the per-line attribute roundtrip proofs.  **`3a7c86e`** introduces `IntDecRat` / `NatDecRat` refinement records (DecRat + `T (predicateᵇ value)` witness, mirroring Identifier T3-fixed pattern) — `Aletheia/DBC/DecRat/Refinement.agda` (~190 LOC) plus migration of `AttrType` / `AttrValue` integer/nat fields, and a new `Properties/Attributes/Common.agda` (~190 LOC) foundation for the per-line proofs.  JSON wire / cantools wire formats preserved by converting at boundaries.  **`c884e69`** subsumes `parseInt` into `parseDecRat = parseDecRatFrac <|> parseDecRatBareInt` (frac form first — `<|>` left-bias keeps `42.5` from being split into bare-int `42` + leftover `.5`).  Internal proofs renamed `parseDecRat-roundtrip-*` → `parseDecRatFrac-roundtrip-*`; new public `parseDecRat-roundtrip-suffix` wraps via `alt-left-just`.  **`7a44c87`** completes the symmetry: `parseIntDecRat` / `parseNatDecRat` (`parseDecRat >>= λ d → ifᵀ predicateᵇ d then mkRefined else fail`) replace `parseInt` / `parseNatural` in `parseIntType` / `parseHexType` — every DBC numeric slot now flows through `parseDecRat`.
- **Layer 3 Commit 3c.0 foundation ✅** (this session, 2026-04-26, `2bee3e5` + `cd723f2`): closes the parser-side roundtrip primitives Common.agda will compose with for 3c per-line attribute proofs.  **`2bee3e5`** ships `parseDecRat-bareInt-roundtrip-suffix : ∀ z pos suffix → SuffixStops isDigit suffix → '.' ≢ headOr suffix '_' → parseDecRat pos (showInt-chars z ++ suffix) ≡ just (mkResult (fromℤ z) ...)` (~430 LOC incl. helpers `headOr`/`≢→≡ᵇ-false-ℕ`/`≢→≈ᵇ-false`/`char-dot-fail-on-non-dot`/`canonicalizeDecRat-zero-exp`/`alt-right-nothing-here`/`bind-nothing-here`/`parseDecRatFrac-fails-+/-neg`/`parseDecRatBareInt-roundtrip-+/-neg`); composes via `alt-right-nothing` over a `parseDecRatFrac` failure (proven by dispatch on `headOr`) and `parseDecRatBareInt` success.  Plus `Refinement.agda` bridge lemmas `fromℤ-intDecRatToℤ` and `fromℕ-natDecRatToℕ` (5-case structural with `()` absurd patterns).  **`cd723f2`** lifts to refined parsers: `parseIntDecRat-roundtrip-suffix` and `parseNatDecRat-roundtrip-suffix` (~135 LOC) via `bind-just-step` ▸ `ifᵀ-witness` (witness pinned via `subst T (sym isIntegerᵇ-fromℤ) tt` / `subst T (sym isNonNegIntegerᵇ-fromℕ) tt`) ▸ `mkIntDecRatFromℤ-intDecRatToℤ` / `mkNatDecRatFromℕ-natDecRatToℕ` recovery.  **Commits 3c.1+ per-line (TaskList #2–#6: parseAttrDef/parseAttrDefRel + parseRawAttrDefault + parseRawAttrAssign/parseRawAttrRel + parseAttrLine 5-way `<|>` composer + facade wiring) pending — next session resumes here.**  Commits 3d (messages: BO_ + inner SG_ many) pending.
- **Layer 4 pending** — top-level aggregator induction over the `DBC` record + the owed char-class-disjointness bridge lemmas (`isIdentStart→¬isHSpace`, `isIdentCont→¬isHSpace`, `isIdentCont→¬isNewlineStart`) plus `showInt-chars-head-non-hspace` (locally provable, ~15L).

**Module count:** 168 Agda modules — see Module Safety Flag Breakdown above.  Net +2 vs 166 post-3b: `Aletheia/DBC/DecRat/Refinement.agda` (`--safe --without-K`) + `Properties/Attributes/Common.agda` (`--without-K` only — transitively imports `Substrate/Unsafe.agda` via `Lexer.agda`).

**Cross-binding parity roadmap:** [docs/development/PARITY_PLAN.md](docs/development/PARITY_PLAN.md), locked after R17. Active deferrals (R17-DEF-1..6, B.3.d Layer 4 owed lemmas, B.3.d-gated cantools drop) tracked in memory under `project_*` files.