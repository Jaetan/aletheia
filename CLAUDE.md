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

**Exceptions**:
- If postulate is truly needed (rare), create separate `*.Unsafe.agda` module
  - Remove `--safe` flag ONLY in that module
  - Document why postulate is needed
  - Must be replaced with proof before production use

**Enforcement**:
- Build system checks all modules have --safe flag
- CI/CD should verify no unsafe modules in production paths
- Code review checklist includes verifying flags

**Current Status**: ✅ All 103 Agda modules use `--safe --without-K`

### Module Safety Flag Breakdown

**By flag combination** (103 total):
- **99 modules**: `--safe --without-K` (standard safe modules)
- **4 modules**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)

**All 103 modules use `--safe`**. No modules require `--sized-types`.

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

- **aletheia.agda-lib**: Agda library configuration (depends on standard-library-2.3)
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
- Two modules use `--no-main` (Parser/Combinators.agda, Main.agda — binary entry point is in Haskell)
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

The C++23 binding lives in `cpp/` and wraps `libaletheia-ffi.so` via `dlopen`:
- **14 public headers** in `include/aletheia/`: `aletheia.hpp`, `backend.hpp`, `check.hpp`, `client.hpp`, `dbc.hpp`, `enrich.hpp`, `error.hpp`, `excel.hpp`, `log.hpp`, `ltl.hpp`, `response.hpp`, `types.hpp`, `validation.hpp`, `yaml.hpp`
- **8 source files** in `src/`: `client.cpp`, `enrich.cpp`, `excel.cpp`, `ffi_backend.cpp`, `json_parse.cpp`, `json_serialize.cpp`, `mock_backend.cpp`, `yaml.cpp`
- **5 test files**: `static_tests.cpp` (compile-time), `unit_tests.cpp` (mock backend + Catch2), `integration_tests.cpp` (threads + Catch2), `yaml_tests.cpp`, `excel_tests.cpp`
- **Design**: `IBackend` interface abstracts FFI boundary; `MockBackend` replays JSON for testing; strong types everywhere (`std::byte`, validated newtypes, `std::expected`)
- **Observability**: Custom `Logger` class (`log.hpp`, ~80 lines) — callback-based structured logging with 12 event types matching Go's slog; zero-cost when null (default)
- **RTS cores**: `make_ffi_backend(path, rts_cores)` — default 1; once-per-process with mismatch warning
- **Build**: `cd cpp && cmake -B build && cmake --build build && ctest --test-dir build`
- **Style**: `.clang-format` + `.clang-tidy` enforce naming/formatting; C++23, targets g++>=14 and clang>=21

### Go Binding

The Go binding lives in `go/` and wraps `libaletheia-ffi.so` via cgo + dlopen:
- **17 source files** in `go/aletheia/`: `backend.go`, `check.go`, `client.go`, `dbc.go`, `doc.go`, `enrich.go`, `error.go`, `excel.go`, `ffi.go`, `ffi_nocgo.go`, `json.go`, `loader.go`, `ltl.go`, `mock.go`, `result.go`, `types.go`, `yaml.go`
- **12 test files**: `batch_test.go`, `check_test.go`, `dbc_test.go`, `enrich_test.go`, `error_test.go`, `excel_test.go`, `helpers_test.go`, `mux_test.go`, `options_test.go`, `stream_test.go`, `types_test.go`, `yaml_test.go` (243 tests, mock backend)
- **Design**: `Backend` interface abstracts FFI; `MockBackend` replays JSON for testing; `FFIBackend` loads .so via `dlopen`/`dlsym` with C trampolines; strong types (`[]byte` payload with DLC-based validation, validated newtypes for CAN ID / DLC, sealed interfaces for CanID/Predicate/Formula)
- **Observability**: `slog` structured logging via `WithLogger` option (12 event types); `ViolationEnrichment.CoreReason` carries Agda core reason strings
- **RTS cores**: `NewFFIBackend(path, WithRTSCores(n))` — functional option, once-per-process with mismatch warning
- **Concurrency**: `Client` is goroutine-safe (`sync.Mutex`), double-close safe, GHC RTS init thread-pinned (`LockOSThread`)
- **Build/test**: `cd go && go test ./aletheia/ -v -count=1 -race`
- **Style**: `gofmt` + `go vet` clean; godoc on all exports

### Haskell FFI Layer

The Haskell FFI layer is a single file:
- **AletheiaFFI.hs** (~130 lines): `foreign export ccall` wrappers → `libaletheia-ffi.so`

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

**Build failures**: `cabal run shake -- clean && cabal run shake -- build`

**Python issues**: Verify venv active (`which python3` → should show `.../.venv/bin/python3`)

**Agda module not found**: Check `~/.agda/libraries` lists standard-library path and `~/.agda/defaults` contains "standard-library"

**MAlonzo name mismatch**: Build provides exact sed command - just run it

**Type-checking timeout**: Always use `agda +RTS -N32 -RTS` for parallel GHC

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
  - Used in all 67 Aletheia modules
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

### Code Style

**Agda:**
- Naming: Follow stdlib conventions
- Indentation: 2 spaces
- Line length: Aim for 80 characters, max 100

**Haskell:**
- Style: Follow standard Haskell style
- Keep it minimal: Haskell shim should stay minimal (~130 lines)

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

**Latest (2026-04-10):** AGENTS.md review round 6 — 24 findings across Agda (14), Go (4), C++ (3), Python (2). Commit `57a0358`. Agda: wired dead `ExtractionErr` into categorizeResult/categorizeIndexed (updated completeness proof with per-constructor cases); removed dead imports (Vec `_∷ᵥ_` in CrossOrder, redundant `z≤n; s≤s` in Disjointness); documented dead branches (dlcToBytes catch-all, bytesToDlc nothing, extractSignal nothing, EOS synthetic timestamp 0); naming consistency (`_++ₛ_` in Prelude, `showℕ` in Format, cleaned bare Rational imports); extracted `parseObjectList` combinator with index threading for NotAnObject errors — directly recursive (not where-block) so MetadataRoundtrip proofs can generalize over any starting index via `*-list-go n` helpers; removed redundant wrapped-error matches in errorCode; extracted `parseCanIdDlc`/`parseBytePayload` in Routing; replaced hand-rolled `T-irrelevant` with stdlib re-export. Go: rationale comment for `maxExtractCache=256`; fixed "on linux" duplication in ffi_nocgo.go; converted hot-path Debug calls to `slog.LogAttrs`; added error_event.sent/remote_event.sent logging. C++: fixed "backward compatibility" → "testability" comment; added error_event.sent/remote_event.sent logging; added `Error` LogLevel + `error()` method. Python: fixed absolute→relative import in can_log.py; sorted EOS extraction iteration order for cross-binding parity. MAlonzo mangling fix: `extractionErrorCodeToℕ_142 → _144`. 8 NO-FIX deferrals (bitLength admits 0, metric window/startTime raw ℕ, lastObserved ℕ, PropertyState.index Fin, SimplifySound/SoundOps repetitive, Satisfied stability lemma, _client.py marginal length). Gates: check-properties clean, cabal build 1m34s (218 MAlonzo), Python 598/0/0/10.00, C++ 5/5 ctest, clang-format clean, Go 251 -race, go vet + gofmt clean. 24 files changed. 103 Agda modules, all `--safe --without-K`.

**Prior (2026-04-09):** Path G — three-valued Kleene `FinalVerdict` landed. The soundness-but-user-surprising gap where `Always(p)` on a trace that never observes `p`'s signal operationally yielded `Fails` at end-of-stream (while the denotation says Unknown) is closed. `Aletheia.LTL.Incremental.FinalVerdict` gets a new `Unsure : String → FinalVerdict` constructor; `finalizeL` in `LTL/Coalgebra.agda` is rewritten as Kleene K3 logic — `Atomic → Unsure`, `Not/And/Or` combine via K3 truth tables, liveness operators (Eventually/Until/MetricEventually/MetricUntil) still return Fails, safety operators (Always/Release/MetricAlways/MetricRelease) still return Holds. `LTL/Simplify.agda` adds a `finalizesFails : LTLProc → Bool` helper (Unsure returns false); the `Or φ (Eventually ψ) → Eventually ψ` absorption now requires `finalizesFails φ = true` so Unsure no longer justifies collapsing to Fails. Adequacy: `verdictToSV Unsure = Unknown` and `finalize-empty-equiv` in `LTL/Coalgebra/Properties.agda` resolves the empty-trace `Atomic` case to Unknown on both operational and denotational sides; `LTL/Semantics.agda` denotes `Atomic p [] = Unknown` to match. `LTL/SimplifySound.agda` empty-trace And/Or cases are rewritten to delegate to per-verdict helper functions `runL-X-[] a b (finalizeL a) (finalizeL b) refl refl hyp`, which take the two `FinalVerdict` results as explicit parameters — this works around Agda's limitation where nested `with finalizeL a | finalizeL b` scrutinee abstraction does not partially evaluate past intermediate `refl` rewrites under Path G's three-valued codomain. `LTL/Semantics/MTL.agda` four-valued metric combinators updated with Unsure absorption lemmas. **Protocol layer**: `Protocol/Response.agda` adds an `Unresolved` `PropertyResult` constructor (fields: `property_index`, `reason`); `Protocol/Handlers.agda` dispatches `FinalVerdict.Unsure r` to `Unresolved`; `Protocol/ResponseFormat.agda` emits `"status": "unresolved"` in the JSON results. **Bindings**: Python `protocols.py` adds `"unresolved"` to the `PropertyResultEntry.status` Literal and `_client.py` extracts reason + enrichment for unresolved entries; `cli.py` prints a separate "Unresolved" section in `check` output with `total_unresolved`/`unresolved` fields in the JSON summary and `status ∈ {"violations", "unresolved", "pass"}`. C++ `response.hpp` adds `Verdict::Unresolved`, `json_parse.cpp parse_stream_result` maps `"unresolved"` → `Verdict::Unresolved`, `client.cpp end_stream` enriches both Fails and Unresolved and logs them with separate `numFails`/`numUnresolved` counts. Go `result.go` adds `Unresolved` to the `Verdict` iota with `.String() = "unresolved"`, `json.go parsePropertyResult` maps the JSON string, `client.go EndStream` handles the new case via switch. Tests updated: `python/tests/test_eos_finalization.py` — 4 tests (`test_changed_by_never_one_frame`, `test_always_never_observed_one_frame`, `test_always_never_observed_many_frames`, `test_eventually_never_observed_is_consistent`) were pinning the pre-Path-G `"holds"`/`"fails"` behaviour and now assert `"unresolved"`; class docstring rewrites the proof walks in K3 terms (`Unsure ∧ Holds = Unsure`, `Unsure ∨ Fails = Unsure`). New `test_end_stream_unresolved_verdict` in `test_unified_client.py`, `TestStreamingLTL_Unresolved` in `go/aletheia/stream_test.go`, third `"unresolved"` result entry in the `parse_stream_result complete` C++ Catch2 test, Go `TestVerdictString` Unresolved branch, C++ `static_asserts` for `Verdict::Unresolved` distinctness. **Drive-by**: 154 pre-existing clang-format violations across 7 C++ files (`backend.hpp`, `backend.cpp`, `client.cpp`, `enrich.cpp`, `ffi_backend.cpp`, `json_parse.cpp`, `integration_tests.cpp`) fixed via `clang-format -i` per `feedback_fix_tool_gate_violations.md` — mostly one-line `if (s == "...") return …;` statements violating `AllowShortIfStatementsOnASingleLine: Never`. Also caught a lurking bug from the earlier Path G protocol work: `cpp/src/json_parse.cpp parse_stream_result` had the enum and test updated but the parser switch still threw `"Unknown verdict status: unresolved"` — the third result entry in the test exposed it. Gates: Agda type-check clean, cabal shake build in 1m33s (218 MAlonzo modules), Python 553 passing, basedpyright 0/0/0, pylint 10.00/10, C++ 5/5 ctest (142 unit + 14 integration + 33 YAML + 47 Excel), clang-format clean, Go 251 passing with `-race`, go vet + gofmt clean. 11 Agda files modified (no new modules); 103 Agda modules total, all `--safe --without-K`.

**Prior (2026-04-08):** Deferred non-blocker §12.1 closed — JSON parser now enforces `PhysicallyValid` at parse time, lifting the conditional `parse-format-parse-given-PV` theorem to an unconditional `parse-format-parse`. `DBC/JSONParser.agda` adds a top-level `physicalGate` helper (LE = identity, BE = three nested `ifᵀ` checks: `1 ≤ᵇ bl`, `csb + bl ∸ 1 <ᵇ frameBytes * 8`, `bl ∸ 1 ≤ᵇ csb`) that runs once per signal inside `parseSignalFields`; each failed check emits a distinct `ParseError`. `parse-wellformed` is strengthened from `WellFormedDBC` to `WellFormedDBCRT`, with witnesses flowing through a new `parseMessageList-pv` → `parseMessage-pv` → `parseSignalList-pv` → `parseSignalFields-pv` chain that mirrors the existing `-wf` chain. `PhysicallyValid` is refactored in `Formatter/WellFormed.agda` from a 4-field record to a 2-constructor data type (`pv-LE` for LittleEndian signals, `pv-BE` for BigEndian carrying the three bound proofs) — the old record form rejected `startBit = 0`, `bitLength = 1` LE signals via an over-strong `msb-ge-len` constraint. `signal-roundtrip-go` in `Formatter/SignalRoundtrip.agda` pattern-matches on `pv-BE`/`pv-LE`; the BE clauses added three `rewrite ≤→≤ᵇ-true`/`<→<ᵇ-true` calls to discharge the gate's `ifᵀ` branches. New `ParseError` variants: `SignalBitLengthZero` (code `parse_signal_bit_length_zero`), `SignalOverflowsFrame ℕ ℕ ℕ` (code `parse_signal_overflows_frame`), `SignalMSBBelowBitLength ℕ ℕ` (code `parse_signal_msb_below_bit_length`). Error code count 41 → 44, with mirrors added to `python/aletheia/protocols.py`, `cpp/include/aletheia/error.hpp` + `cpp/src/json_parse.cpp`, and `go/aletheia/error.go`. Behaviour change: `test_big_endian_signal_exceeds_dlc` in `python/tests/test_dbc_validator.py` updated — BE signals that overflow the frame are now caught at parse time (`parse_signal_overflows_frame`) rather than downstream by the validator's `signal_exceeds_dlc` check; the validator's BE overflow check becomes provably redundant for parser-validated DBCs. All gates green: Agda type-check clean, cabal build in 1m36s (218 MAlonzo modules), Python 546, basedpyright 0/0/0, pylint 9.97/10 (only pre-existing design-level R/C warnings remain), C++ 5/5 ctest, Go -race + vet + gofmt. Benchmarks: all within ±5% of 2026-04-08 post-fix baseline — `physicalGate` runs only at parse time (one-shot DBC load), not on the streaming hot path, so there is no throughput impact. 95 Agda modules.

**Prior (2026-04-08):** Deferred non-blockers 15.1/15.2 closed — both large `Properties.agda` files are now curated facades that re-export per-topic submodules via `open import X.Y public using (...)` blocks. **15.1** `src/Aletheia/CAN/Encoding/Properties.agda` (was 1581 lines) split into three submodules and a 78-line facade: `Properties/Arithmetic.agda` (Layer 2 ℕ↔ℤ + Layer 3 ℤ↔ℚ algebraic bridge lemmas), `Properties/Roundtrip.agda` (Layer 4 composition + `WellFormedSignal` record), `Properties/Disjoint.agda` (bit preservation under disjoint injection, including mixed byte-order physical disjointness). **15.2** `src/Aletheia/Protocol/FrameProcessor/Properties.agda` (was 1256 lines) split into five submodules and a ~150-line facade: `Properties/Step.agda` (223 lines, P1-P8/P14-P15 state machine guards + Streaming decomposition + Ack/Violation soundness/completeness), `Properties/Cache.agda` (197 lines, P10-P13/P23-P26 cache update decomposition + monotonicity / timestamp-bound preservation), `Properties/Handlers.agda` (112 lines, P16-P22 FFI link + read-only handler state preservation), `Properties/Bounded.agda` (625 lines, P9 `mkPredTable` faithfulness + P27 atom-index bound through `simplify`/`stepL`), `Properties/Monotonic.agda` (209 lines, P28-P29 timestamp monotonicity + trace-level lift via `checkedFrames`/`HeadBounded`). Dependency graph: `Handlers` and `Monotonic` import from `Step`; `Bounded` and `Cache` are leaves. The facade re-exports all 68 public names (15 Step + 10 Cache + 7 Handlers + 23 Bounded + 13 Monotonic) so external consumers import unchanged — `LTL.Adequacy.WarmCache` still imports `AllBelow` and `mkPredTable-lookup` from the top-level path. MAlonzo no-impact: neither facade is in `AletheiaFFI.hs`'s import graph and the mangled names depend only on submodule paths, not facade structure. Total line count across FrameProcessor submodules + facade is 1516 (was 1256 monolithic) — the overhead is facade headers and per-submodule imports, traded for faster IDE jump-to-definition and independent re-checking per layer. All gates green: Agda type-check clean, cabal build in 1m51s, Python 546 passing, C++ 5/5 ctest, Go -race + vet + gofmt clean. 95 Agda modules.

**Prior (2026-04-08):** Deferred non-blocker 14.1 closed — `src/Aletheia/Main.agda` is now a curated public facade. The old two-line `open import Main.JSON public` / `open import Main.Binary public` is replaced with explicit `using (...)` lists grouped into seven sections: FFI entry points; state machine (`StreamState` + constructors, `initialState`, `getDBC`, `checkMonotonic`, `handleDataFrame`, `handleTraceEvent`); command dispatch (`StreamCommand` + 9 ctors, `Response` + 8 ctors, `processStreamCommand`); frame/trace/DLC types (`CANId`, `CANFrame`, `DLC`, `TimedFrame`, `TraceEvent`, `Timestamp`, `TimeUnit`); error types and inspection (the `Error` sum + per-domain ADTs, `formatError`/`errorCode`); JSON and response formatting. Three `Error` names would collide (`Aletheia.Error.Error`, `Response.Error`, `TraceEvent.Error`) — the two constructors are re-exported as `ResponseError` and `TraceError` via `renaming`, leaving the canonical top-level `Error` name free. `src/Aletheia/Main/JSON.agda` cleanup: `wrapJSON`, `tryParseCommand`, `dispatchCommand`, `handleParsedJSON` are now in a `private` block (matching `Main/Binary.agda`); `processJSONLine` stays public with its NOINLINE pragma. MAlonzo numbering is unchanged — `d_processJSONLine_64` still exists with the same number (verified by reading generated `build/MAlonzo/Code/Aletheia/Main/JSON.hs`) and `AletheiaFFI.hs` continues to reference it without modification; MAlonzo compiles private Agda definitions to numbered Haskell symbols regardless of visibility. 2 files touched. All gates green: Agda type-check clean, cabal build in 2m17s, Python 546 passing, C++ 5/5 ctest, Go -race + vet + gofmt clean.

**Prior (2026-04-08):** Deferred non-blocker 11.1 (`mkPredTable` atom index → `Fin (length atoms)`) re-analysed after the Timestamp commit and kept deferred on performance grounds. MAlonzo compiles `Fin n` as a unary Peano chain (`data T_Fin_10 = C_zero_12 | C_suc_16 T_Fin_10`) — k heap cells per value, one dereference per pattern match — whereas the current `ℕ` index compiles via BUILTIN to Haskell `Integer` with native `eqInt`/`subInt`. `mkPredTable` runs per frame on the streaming loop (its closure invoked by `stepL` for every Atomic cell), so this is the same class of hazard as the `Dec`-vs-`Bool` regression from commit `5aa345e` (30–65% throughput loss). A ~40-line comment block above `mkPredTable` in `src/Aletheia/Protocol/StreamState/Internals.agda:91` now records the refactor option, the hazard, structural cost (~8 files, four-valued `agreement` shape change, FFI mangling re-verification), and the recommendation to leave alone unless benchmarked first. `project_system_review_deferred.md` 11.1 updated with the hazard summary; new `feedback_in_source_deferral_notes.md` captures the general principle "record deferred MAlonzo hot-path refactor hazards in-source, not only in memory". Type-check clean; no runtime code change.

**Prior (2026-04-08):** Timestamp dimensional refinement complete — closes deferred non-blocker 10.1 from `project_system_review_deferred.md`. `TimedFrame.timestamp` and both `TraceEvent` error/remote timestamps now have type `Timestamp μs`, a single-constructor record with an erased (`@0`) `TimeUnit` phantom. New module `Aletheia.Trace.Time` defines `TimeUnit` (`ns`/`μs`/`ms`/`s`), the `Timestamp (@0 u : TimeUnit)` record with `tsValue : ℕ` projection, unit-preserving operators (`_∸ᵗ_`/`_≤ᵗ_`/`_≤ᵗᵇ_`/`_≡ᵗᵇ_`/`_∸ₜₙ_`), and retraction lemmas. MAlonzo strips the erased unit entirely: `newtype T_Timestamp_18 = C_mkTs_26 Integer` is the same shape as the old `Timestamp = ℕ`, so zero hot-path cost (confirmed — benchmarks at or above the 2026-04-08 post-fix baseline). Two Agda types `Timestamp μs` vs `Timestamp ms` are now distinct and cannot be mixed without explicit conversion. `Protocol/FrameProcessor/Properties.agda` and `StreamState.agda` use a new `timestampℕ : TimedFrame → ℕ` helper at arithmetic/comparison boundaries (metric LTL operators, `checkMonotonic`, `updateCacheFromFrame`). `AletheiaFFI.hs` constructs `AgdaTime.C_mkTs_26 (toInteger timestamp)` in all three FFI entry points; MAlonzo renumbered the `TimedFrame`/`TraceEvent` constructor mangling to `C_constructor_32`/`C_Error_38`/`C_Remote_40` as a side-effect of the new runtime-relevant field. The unit is fixed at `μs` across all bindings — the parameter exists for theorem parameterisation, in-source documentation, and future extensibility to higher-frequency buses. 13 modified files (1 new + 12 edited). 95 Agda modules. SignalCache `lastObserved : ℕ` intentionally left unchanged — internal bookkeeping outside 10.1 scope. All correctness gates green: Python 546, C++ 5/5 ctest, Go -race + vet + gofmt, basedpyright 0/0/0, cabal build in 1m38s.

**Prior (2026-04-08):** Frame-building throughput regression RESOLVED — root cause identified and fixed via Bool-valued bitmask fast path with full equivalence proofs. Bisection pinpointed commit `5aa345e` (not `8eb071c` as initially suspected — the binary FFI path bypasses `Handlers.agda` entirely via `processBuildFrameBin` → `buildFrameByIndex`). That commit had replaced O(1) `rangesOverlap` with Dec-valued `physicallyDisjoint?`, whose nested `allBounded` quantifier allocates `Dec` proof terms per bit-pair per frame — MAlonzo's `Integer`-boxing on those allocations caused a 30–65% throughput regression (CAN-FD worst at -64%). Fix: new `signalsPhysicallyOverlapᵇ` Bool-valued check in `DBC/Properties.agda` with precomputed per-signal bit lists hoisted out of the O(m²) pair loop, plus equivalence proofs `physicallyOverlapᵇ-sound` / `physicallyOverlapᵇ-complete` establishing `signalsPhysicallyOverlapᵇ ≡ false ⇔ PhysicallyDisjoint`. Recovery: CAN 2.0B frame building +23–37% and CAN-FD frame building +107–147% vs the regression state. All gates green: Python 546, C++ 5/5 ctest, Go -race + vet + gofmt, basedpyright 0/0/0, cabal build. Memory: `project_frame_building_regression_2026_04_07.md`, `feedback_hot_path_refactor_benchmark.md`. AGENTS.md Category 16 updated with the Dec-vs-Bool cost-model lesson. Side observation: the post-fix run has Go slightly ahead of C++ on Frame Building (+11% CAN 2.0B, +13% CAN-FD) — Frame Building is a near-tied race because it's the benchmark with the smallest Agda kernel and the largest binding-layer cost, so glibc `malloc` and `std::unordered_map` overhead in the C++ binding's `build_frame` become visible; Stream LTL and Signal Extraction remain clearly C++-dominant. Not a C++ vs Go performance truth, just benchmark geometry — see `project_cpp_vs_go_frame_building.md`.

**Prior (2026-04-07):** Phase 5.1 review round complete — 11 findings (C1/C2/C3 + H1–H6 + D1–D3 + X1/X2) closed on top of the 14/14 Phase 5.1 items. Review highlights: **C1** monotonic bridge lemma from `handleDataFrame` to trace-level `Trace.CANTrace.Monotonic` (closes the enforcement ↔ theorem-hypothesis gap). **C3** warm-cache agreement chain — `evalPredicate-cache-definite` → `lookupAtom-warm` → `warm-cache-table-definite` → `warm-cache-bounded-twovalued` → `agreement-bounded` → `warm-cache-agreement`, composing Property 27 with cache warmness to discharge `agreement`'s `TwoValued` precondition on steady-state hot paths. **H3** two-sided `sound-transport` combinator extracted in `Adequacy.agda`. **H5** legacy `inspect` → `with expr in eq` migration in 3 files. **D1+D2+D3** dedup of `buildResult`/`updateResult`/`formatResult` via single `frameResponse : String → ∀ {n} → FrameError ⊎ Vec Byte n → Response` helper with `Data.Sum.map₂` for update handlers. **H6** fuel justification docs for `walkMux` and `checkPresenceP`. **X2** Agent D deferred non-blockers recorded in `project_system_review_deferred.md`. All correctness gates green: Python 546, C++ 5/5 ctest (14 integration), Go -race + vet + gofmt, basedpyright 0/0/0, cabal build. 92 Agda modules, all `--safe --without-K`.

**Prior (2026-04-07):** Monotonic predicate enforcement complete — Phase 5.1 14/14. `handleDataFrame` now enforces timestamp monotonicity in Agda via `checkMonotonic`; backward frames rejected with new `NonMonotonicTimestamp` HandlerError (code `handler_non_monotonic_timestamp`). Repurposes the previously-vestigial `prev` field in `Streaming` as the monotonicity anchor (proven by `handleDataFrame-rejects-regress`). 6 new properties in `FrameProcessor/Properties.agda` Property 28. Duplicated runtime checks removed from Python `_client.py`, C++ `client.cpp`/`client.hpp`, and Go `client.go` — Agda is now single source of truth. 41 error codes total (was 40).