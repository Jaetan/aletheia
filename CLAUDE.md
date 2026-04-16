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

**Current Status**: ✅ All 120 Agda modules use `--safe --without-K`

### Module Safety Flag Breakdown

**By flag combination** (120 total):
- **116 modules**: `--safe --without-K` (standard safe modules)
- **4 modules**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)

**All 120 modules use `--safe`**. No modules require `--sized-types`.

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
- **Observability**: Custom `Logger` class (`log.hpp`, ~90 lines) — callback-based structured logging with 16 event types matching Go's slog; zero-cost when null (default)
- **RTS cores**: `make_ffi_backend(path, rts_cores)` — default 1; once-per-process with mismatch warning
- **Build**: `cd cpp && cmake -B build && cmake --build build && ctest --test-dir build`
- **Style**: `.clang-format` + `.clang-tidy` enforce naming/formatting; C++23, targets g++>=14 and clang>=21

### Go Binding

File/test inventory lives in [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics). This section covers design only.

The Go binding lives in `go/` and wraps `libaletheia-ffi.so` via cgo + dlopen:
- **Optional Excel package**: `go/excel/` is a separate Go module (separate `go.mod`) that pulls in the heavy `xuri/excelize` dependency chain; depend on it only if you need the Excel loader.
- **Design**: `Backend` interface abstracts FFI; `MockBackend` replays JSON for testing; `FFIBackend` loads .so via `dlopen`/`dlsym` with C trampolines; strong types (`[]byte` payload with DLC-based validation, validated newtypes for CAN ID / DLC, sealed interfaces for CanID/Predicate/Formula)
- **Observability**: `slog` structured logging via `WithLogger` option (16 event types); `ViolationEnrichment.CoreReason` carries Agda core reason strings
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

**Current**: Phase 5 — Optional Extensions. Binary frame API (4.3x CAN 2.0B, 9.1x CAN-FD), CAN-FD, C++/Go bindings, cross-language benchmarks all complete. Four-tier check interface with full cross-language parity. See PROJECT_STATUS.md for detailed metrics and review history.

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
  - Used in all 120 Aletheia modules
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
1. Ensure code type-checks: `agda +RTS -N32 -RTS src/Aletheia/Main.agda`
2. Build succeeds: `cabal run shake -- build`
3. Tests pass:
   - Python: `cd python && python3 -m pytest tests/ -v`
   - C++: `cd cpp && cmake -B build && cmake --build build && ctest --test-dir build`
   - Go: `cd go && go test ./aletheia/ -v -count=1 -race`

---

## Current Session Progress

See [PROJECT_STATUS.md](PROJECT_STATUS.md) for phase status and deliverables.

See [.session-state.md](.session-state.md) for session recovery, next steps, and current work context.

**Latest (2026-04-16):** AGENTS.md review round 14 — cross-binding correctness + PhysicalValue precision. Commit `a3208aa` (80 files, +934/−529). Section A HIGH (9): C++ `parse_frame_response` type check (A1), Python binary zero-denom raise (A2), `FRAME_SIGNAL_VALUE_OUT_OF_BOUNDS` error code added to C++/Go (A3), Python CLI DLC-vs-bytes CAN-FD fix (A4), Shakefile stdlib-mismatch (A5), Python enrichment zero-denom guard (A6), **C++ PhysicalValue double→Rational** across 19 files (A7 — exact precision matching Python's `Fraction`), WNext operator across 22 Agda files + all bindings (A8), evaluate-before-update formal proof (A9). Section B MEDIUM (13): Go cgo bounds checks (B1), Go mutable maps→accessor functions (B2), C++ MockBackend binary heuristic (B3), C++ symmetric validation (B4), backend.warning cross-binding vocab (B5), Python finalization parsing (B6), Agda ValidationFailed structured (B7), docs JSON→binary-FFI qualifier (B8), PROTOCOL.md unresolved status (B9), aletheia.h send_error/send_remote (B10), CLI.md mux-query (B11), test count fix (B12), Agda version + 16 log events (B13). Section C LOW (23): Go dead code + interface{}→any + naming (C1-C3), C++ SPDX headers + naming + Rational validation + unified MessageKey + MockBackend default test (C4-C8), Python immutability + naming + --version + test gaps (C9-C12), Agda dedup + patterns + combinators (C13-C17), Docs cross-ref consolidation (C18). 619 Python tests (+2), 268 C++ tests (+4), 276 Go tests, 1163 total. pyright 0/0/0, pylint 10.00, ctest 5/5, go -race clean. Benchmarks within WSL2 variance of R13.

**Prior (2026-04-16):** AGENTS.md review round 13 — docs-dominant round. Section A: count drift (PROJECT_STATUS C++ 40 files / Python 22 modules / Go 16+15 tests; CLAUDE.md C++/Go blocks demoted to cross-references with design-only prose). Section C: Python architecture (shallow-copy docstring in `client/_client.py`, lazy-import boundary in `aletheia/__init__.py`, 3-point coupling block in `dsl.py`, pyproject gate-mapping + re-evaluation trigger comments, CLI `mux-query` subcommand + 11 tests). `Predicate.next()` / `Property.next()` **kept but relocated** to end-of-class under a "Discouraged in CAN analysis" banner — user correction: "discouraged ≠ deprecated". Section D (28 items): PROTOCOL.md Common Error Codes table (50 codes, 6 domains), DESIGN.md "Why Agda/Haskell/JSON" rationale, QUICKSTART.md "Prerequisites & first build", CLAUDE.md "Common newcomer mistakes", README/PITCH qualified throughput numbers, PROJECT_STATUS Key Metrics with Measured column, INTERFACES side-by-side parity code + Structured Logging section, PYTHON_API `data` construction examples, DISTRIBUTION equivalence comments. Phase 6 added toolchain upgrade item (basedpyright / pylint upper-pin refresh). 617 Python tests (was 606, +11 from mux-query suite), pyright 0/0/0, pylint 10.00, ctest 5/5, go -race clean, Agda full build green. Benchmarks vs R12 post-fix baseline (Python Stream LTL 70,056 fps): R13 75,914 fps = **+8.4%**; no regression gate crossed. Other lanes within WSL2 variance.

**Prior (2026-04-15):** AGENTS.md review round 12 — 92 files touched in single commit. Agda AGDA-25 polymorphic `collectAtomsAcc`, Shakefile `check-erasure` phony, C++ test split (7 focused TUs + `test_helpers.hpp`), Go `go.work` + `concurrent_test.go`, Python structured `client/_log.py` + `benchmarks/_common.py` + `tests/test_error_code_sync.py`, Docs D1-D6. Commits `60661a1` (R12) + `1e40b4d` (post-bench `log_event` `isEnabledFor` fast-path fix). First-run Python Stream LTL regressed −16.1%; root-caused to `log_event` allocating unconditionally on hot path; post-fix Python Stream LTL +10.9% (63,173→70,056 fps). 606 Python tests, pyright 0/0/0, pylint 10.00, all ctest suites pass, go -race clean, Agda full build + 3 check-* phonies green.

**Prior (2026-04-15):** R11 — 6 batches (`bf238b3` + `222b662`). Stream LTL +2.4% C++ / +3.4% Go / +8.9% Python vs 2026-04-11 baseline.

**Prior (2026-04-14):** R10 — 68 findings: Agda (13), Go (7), C++ (12), Python (13), Docs (20). Hot-path +10.8% Stream LTL. Commit `f227d88`.

**Prior (2026-04-14):** R9 — 56 findings, commit `7203d9f`. R8 partial (`6ab5639`). Squash-merged phase-5.1→main as `a8ba94c`.

**Prior (2026-04-11):** AGENTS.md review round 7 — 51 findings across Agda (22), Go (18), C++ (9), Python (5). Commit `cdd5821`.

**Prior (2026-04-10):** AGENTS.md review round 6 — 24 findings across Agda (14), Go (4), C++ (3), Python (2). Commit `57a0358`.

**Prior (2026-04-09):** Path G — three-valued Kleene `FinalVerdict` with `Unsure` constructor.

**Prior (2026-04-08):** Closed deferred items, frame-building regression fixed. 95 Agda modules.

**Prior (2026-04-07):** Phase 5.1 complete (14/14). 92 Agda modules.