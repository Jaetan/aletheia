# CLAUDE.md

Guidance for Claude Code (claude.ai/code) when working in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). Core logic in Agda with correctness proofs, compiled to Haskell, exposed through Python, C++, and Go APIs. Phase status: [PROJECT_STATUS.md](PROJECT_STATUS.md). Mission: [docs/PITCH.md](docs/PITCH.md).

## Development Environment

**Must be preserved across session compression.**

- Agda binary: `/home/nicolas/.cabal/bin/agda`
- Shell: `/usr/bin/fish` (config at `/home/nicolas/.config/fish/config.fish`)
- User binaries: `/home/nicolas/.local/bin`; libraries: `/home/nicolas/.local/lib`
- **Single Python venv**: exactly one, at `python/.venv` (Python 3.14). Run every Python gate via `python/.venv/bin/...` (never system `python3`). Never create a second venv (e.g. a repo-root `.venv`). Enforced by `tools/check_venv_convention.py` (a `run_ci.py` gate); the rule's canonical statement is in [AGENTS.md § Universal Rules](AGENTS.md#universal-rules-all-languages).
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
  - **C++**: `Mull` 0.34.0 (LLVM-22) — no prebuilt deb ships for LLVM 22, so build from source against system LLVM-22 (Bazel; `clang-22` + `llvm-22-dev`) into `~/.local/bin/` as `mull-{runner,reporter,ir-frontend}-22`. Full grounded recipe (incl. the `MODULE.bazel` ubuntu:24.04→"22" patch) in [docs/operations/MUTATION.md § C++](docs/operations/MUTATION.md); CI caches it (`.github/workflows/pr-heavy-lanes.yml`). The `ALETHEIA_MUTATION` build folds the real-`.so` integration tests into `unit_tests` so FfiBackend is on the mutation surface.
  Each tool's absence is auto-detected by `tools/mutation_run.py` (per-binding skip-with-precise-error); the orchestrator's static gate `tools/check_mutation_setup.py` runs always-on regardless of tool install state.

**Type-check command** (always cap heap):
```bash
/home/nicolas/.cabal/bin/agda +RTS -M16G -RTS src/Aletheia/YourModule.agda
```
- `-M16G`: heap cap; prevents runaway elaboration on the memory-limited WSL2 host. Doubles as a tripwire — bump only when a specific module legitimately needs it. This is the load-bearing flag.
- `-N` (parallel GHC) is optional and gives no measured single-module speedup — even the heaviest modules (Protocol/StreamState.agda, Main.agda) type-check in a few seconds at `-N1`, slightly slower at higher `-N`. Parallelism pays off at the whole-build level (Shake's `shakeThreads=0`), not per module.
- First build compiles stdlib (~20s, cached thereafter).

## Global Project Rules

### AGENTS.md as Coding Standards

[AGENTS.md](AGENTS.md) defines per-language categories, guidelines, and verification commands. **Follow these as coding standards when writing code, not only as review checklists.** Consult the relevant language section before writing/modifying code.

### User Shorthands

When the user's message is just `UPD` (case-insensitive, no other content), interpret it as **"Update session state, memory/feedback, plan/project status, CLAUDE.md/AGENTS.md."** Sweep:
- `.session-state.md` (gitignored — local resume notes)
- `MEMORY.md` + relevant files under `memory/` (open-work pointers; new feedback memories if a generalizable lesson surfaced)
- `PROJECT_STATUS.md` (the roadmap/status surface)
- `CLAUDE.md` (Current Session Progress, module-flag breakdown, anything that drifted)
- `AGENTS.md` (only if a new rule / cross-ref was earned this session)

**Size budget** — after the sweep, check BOTH authoritative doc surfaces and reduce any that is over its limit:
- **CLAUDE.md**: `wc -c CLAUDE.md`, limit **40.0 kB**. If over, compress in the same UPD commit — push narrative detail into the appropriate `memory/project_*.md` file (e.g. `project_review_round20.md`) and replace with a one-line index pointer, mirroring how earlier detail was compressed (e.g. the `970f704` compression of Current Session Progress). The compression IS doc-state sync; do not split into a separate commit.
- **MEMORY.md**: `wc -l ~/.claude/projects/-home-nicolas-dev-agda-aletheia/memory/MEMORY.md` (the agent store, NOT the repo root), limit **200 lines**. If over, compress in-place — move detail from any over-long or multi-line index entry into its `memory/*.md` topic file and collapse the pointer to a single ≤200-char line; merge or drop stale/duplicate/superseded pointers. MEMORY.md lives in the agent memory store under `~/.claude/` (**outside this repo**), so its reduction is an in-place memory edit, NOT part of the UPD git commit.

**UPD is a doc-state sync only.** The resulting commit must contain ONLY doc-sweep edits. Pre-existing uncommitted work (refactors, structural cleanups, prior tasks) goes in its own commit at task completion, never bundled into UPD. See `memory/feedback_upd_scope.md`. Apply the 2-question pre-commit gate (`feedback_pre_commit_scope_check.md`) before committing the doc sweep.

**UPD frequency rule (token-efficiency).** Run UPD **once per coherent batch close** — not after every single step. In one stretch, 19 UPDs landed across 65 commits (29% of all commits were doc syncs); each UPD re-loads CLAUDE.md (~40 KB), so 19 UPDs amount to ~760 KB of CLAUDE re-reads alone. The right cadence: small-batch work updates `.session-state.md` (gitignored — no token cost to other sessions) during the work, then a single UPD at the end syncs CLAUDE.md / MEMORY.md / PROJECT_STATUS.md. Exception: when a batch surfaces a new durable rule (a new `memory/feedback_*.md` worth indexing) AND subsequent work depends on that rule being indexed, that single rule can warrant its own UPD. When in doubt, defer the UPD to the next natural rest-point.

When the user's message is just `READ` (case-insensitive, no other content), interpret it as **"Read the session state, memory/feedback, plan/project status, CLAUDE.md/AGENTS.md."** Sweep (read-only — no edits):
- `.session-state.md` (gitignored — local resume notes)
- `MEMORY.md` + relevant files under `memory/` (open-work pointers, feedback memories)
- `PROJECT_STATUS.md` (the roadmap/status surface)
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

### Module Safety Flags

- Default: every module uses `--safe --without-K`.
- The `Main`-family modules add `--no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda).
- Exactly one module drops `--safe`: the allowlisted `--without-K`-only Unsafe substrate `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, which hosts the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the outer-wrap `parseText-on-formatText` consumer — co-located to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

No modules require `--sized-types`. Run `cabal run shake -- count-modules` for the current module inventory.

## Common Commands

See [Building Guide](docs/development/BUILDING.md). Quick reference:

```bash
# Type-check a single module
cd src && agda +RTS -M16G -RTS Aletheia/YourModule.agda

# Build everything (Agda → Haskell → libaletheia-ffi.so) — incremental + hash-safe
cabal run shake -- build

# Regenerate the foreign-lib MAlonzo module list (after adding/removing an Agda module)
cabal run shake -- gen-ffi-modules

# IWYU import analysis — regenerates the relevant .agdai (no full .hs/.so rebuild)
cabal run shake -- iwyu

# Tests (each from the right cwd)
cd python && python3 -m pytest tests/ -v
cd python && basedpyright aletheia/ benchmarks/ tests/
cd python && pylint aletheia/ tests/ benchmarks/
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
2. Type-check fast: `cd src && agda +RTS -M16G -RTS Aletheia/Parser/Combinators.agda`.
3. Full build: `cabal run shake -- build` (also rebuilds `libaletheia-ffi.so`).
4. Run tests for affected bindings.

Shake tracks Agda dependencies by content hash. A cold full build is ~2m (GHC
compiles every MAlonzo module); an unchanged rebuild is ~0.1s and a one-module
edit ~12s (incremental — cabal recompiles only the changed MAlonzo module + relinks). Adding/removing an Agda module: re-list it with
`cabal run shake -- gen-ffi-modules` (otherwise the build fails naming it, via the
foreign library's `-Werror=missing-home-modules` drift gate). Details:
[BUILDING.md](docs/development/BUILDING.md).

## Key Files

- **aletheia.agda-lib**: Agda library config (pinned stdlib version)
- **Shakefile.hs**: build orchestration (Agda → Haskell → shared library)
- **haskell-shim/aletheia.cabal**: Haskell package + `foreign-library aletheia-ffi`
- **haskell-shim/src/AletheiaFFI.hs**: FFI exports (Python ctypes, C++/Go dlopen)
- **python/pyproject.toml**: Python package config
- **cpp/CMakeLists.txt**: C++23 build (CMake 3.25+, FetchContent for nlohmann/json + Catch2)
- **docs/FEATURE_MATRIX.yaml**: cross-binding feature parity matrix; structural gate tests in `python/tests/`, `go/aletheia/`, `cpp/tests/` fail CI on silent symbol removal. This matrix is the authoritative live parity source; roadmap/status: [PROJECT_STATUS.md](PROJECT_STATUS.md).

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

Wraps `libaletheia-ffi.so` via `dlopen`. `IBackend` interface; `MockBackend` for tests. Strong types (`std::byte`, validated newtypes, `std::expected`). Custom `Logger` (~90L, callback-based, 16 event types matching Go's slog, zero-cost when null). RTS cores via `make_ffi_backend(path, rts_cores)` (default 1, once-per-process with mismatch warning). C++23, **Clang 22** (the supported toolchain — see [BUILDING.md § Toolchain support policy](docs/development/BUILDING.md#toolchain-support-policy)); needs a libstdc++/libc++ with C++23 (`<expected>`). Style: `.clang-format` + `.clang-tidy`.
### Go Binding (`go/`)

Wraps `libaletheia-ffi.so` via cgo + dlopen. `Backend` / `MockBackend` / `FFIBackend` (with C trampolines). Strong types (`[]byte` payload + DLC validation, validated CAN ID / DLC newtypes, sealed CanID/Predicate/Formula interfaces). `slog` via `WithLogger` option (16 event types); `ViolationEnrichment.CoreReason` carries Agda core reason strings. RTS cores via `WithRTSCores` functional option. `Client` is goroutine-safe via a 1-deep channel-token semaphore (`lockCh chan struct{}`) chosen over `sync.Mutex` so that `ctx`-aware `TryLock` cancellation works correctly (see `docs/architecture/CANCELLATION.md`); double-close safe; GHC RTS init thread-pinned (`LockOSThread`). Optional `go/excel/` is a separate Go module pulling `xuri/excelize`; depend on it only for the Excel loader.
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
- **Type-checking timeout**: always `+RTS -M16G -RTS`.
- **`hs_init` failure / `aletheia_init() returned null`**: `.so` built against different GHC than loaded. Rebuild (`cabal run shake -- build`); ensure no stale copy in `$LD_LIBRARY_PATH`.
- **`.so` load failure**: loader checks `_install_config.LIBRARY_PATH` → `LD_LIBRARY_PATH` → `/usr/local/lib`. Regen via `cabal run shake -- install` or set `ALETHEIA_FFI_PATH`.
- **ctypes signature mismatch (Python)**: `.so` and Python package versions drifted. Compare `python -m aletheia --version` vs `strings libaletheia-ffi.so | grep aletheia-ffi-`.
- **DBC validation rejection**: check `ValidationIssue.code` enum — table in [PROTOCOL.md § Error Code Reference](docs/architecture/PROTOCOL.md#error-code-reference). `aletheia validate --dbc <file>` to see all issues.
- **Property formula parse error**: JSON schema is strict (`"operator"` lowercase, predicates under `{"operator": "atomic", "predicate": {...}}`). Compare against `Signal("X").equals(1).to_dict()` output.

## Performance Considerations

- **Parser combinators**: structural recursion on input length, not fuel — fuel breaks termination or blows up type-checking. See `Parser/Combinators.agda`.
- **Type-checking**: always cap the heap `+RTS -M16G -RTS`; `-N` gives no per-module speedup (see the Type-check command note).
- **Hot path**: `Dec`-valued predicates allocate proof terms per call in MAlonzo. Replace with `Bool`-valued fast path + equivalence lemma. See `extractSignalCoreFast` for the pattern.

## Implementation Phases

[PROJECT_STATUS.md](PROJECT_STATUS.md). Current state: Phase 5.1 complete (binary FFI 4.3× CAN 2.0B / 9.1× CAN-FD; CAN-FD; C++/Go bindings; cross-language benchmarks; four-tier check interface with full parity); the parity plan is complete (matrix gates / DBC text parser / cancellation / doc harness / VAL_ promotion). **No active phase**; Phase 6 (Extensions & New Protocols — CLI parity stretch + Rust/Haskell bindings (Haskell native; Rust via .so) + python-can replacement + GHC native bignum + SOME/IP) is the candidate next track, goal-set pinned 2026-05-07 but not started.

---

## Notes for newcomers

Start with the [Project Pitch](docs/PITCH.md) for context.

**Operational pitfalls** (most are caught by build/lint, but easy to trip on first time):
- `Dec`-valued predicates on the streaming hot path: MAlonzo allocates per call. Use `Bool`-valued fast path + equivalence lemma (`extractSignalCoreFast`).
- Fuel-based parser combinators: structural recursion on `length input` only.
- Type-checking without `+RTS -M16G -RTS`: a runaway elaboration can OOM the host instead of failing the build.
- Running tools from the repo root: `pytest` / `basedpyright` / `pylint` need `cd python` first (config picks up nearest `pyproject.toml`).

**Key terms used elsewhere in this file:**
- **"Phase" (capital P) is reserved.** It denotes a **whole-project phase only** — Phase 1 … Phase 6 (see [PROJECT_STATUS.md](PROJECT_STATUS.md) § Project Phases). **Never call the sub-units of any other plan "phases"** — it conflates them with project phases and causes confusion. For the Rust binding's incremental deliverables use **"slice"** (the established term: "tracer-bullet slice", "a later Rust slice"); for other plans use "cluster" / "stage" / "step" / "track". Worked example: the Rust binding's incremental deliverables were organized into *slices*, not phases. (Convention pinned 2026-06-14 at user request.)
- **MAlonzo**: Agda's Haskell backend. `agda --compile` produces a `MAlonzo/` directory of generated `.hs` files; the Cabal package and FFI shared library are built on top. Function names get mangled.
- **`Dec A`**: A type expressing decidability (`yes (a : A) ⊎ no (¬ A)`). Carries a *proof object* at runtime — that's why it allocates on hot paths.
- **`memory/<name>.md`**: a pointer to Claude Code's agent memory store (under `~/.claude/`, **outside this repository**) — written for the agent, not a repo-relative link, so it will not resolve in a repo checkout. The same convention appears in several docs (AGENTS.md, PROJECT_STATUS.md, …). Documented here as an explicit convention 2026-06-12 — it had accreted unratified, not by deliberate decision.

**Code style**: per-language conventions live in [AGENTS.md](AGENTS.md). Don't duplicate here.

**Pre-commit minimum** (doc-only changes): `agda +RTS -M16G -RTS src/Aletheia/Main.agda` → `cabal run shake -- build` → relevant binding tests.

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

**🔧 RTS/EXACTNESS ARC ✅ COMPLETE 2026-07-22 (I.1 #229 → streaming #232 → K.1 #233; three linked closes, several BREAKING JSON-wire entries pending in [Unreleased]).** **I.1 (`186bdcd1`)** — filed item obsolete (guards deleted by the decimal-SSOT sweep); shipped the real successors: one Int64 bound on every wire (`rational_component_magnitude` JSON bound + binary-encoder guard `extraction_value_exceeds_wire_range`, since exact REDUCTION defeats in-range inputs) · Excel raw-stored-value discipline Go+C++ · Py timestamp ceiling + NaN/inf totality + `!!float` accept. **Streaming residency+throughput (`7c43ebb0` #232)** — root-caused an unbounded per-frame cache-thunk leak that killed long monitors; fix bounds residency AND ends up FASTER than pre-arc (CAN-FD +48%), machine-checked verdict-preserving (`handleDataFrame-verdict-preserved`, stepL/adequacy untouched; extract-once shared table driven by the known readable set). **K.1 (`155a8068` #233)** — runtime GHC heap cap (`-M3G`) across all four bindings via `hs_init_with_rtsopts`, SSOT `docs/RESOURCE_BUDGETS.yaml` + `check-rts-runtime` gate, containment-by-abort; also fixed a live GHCRTS-non-safe-option startup crash. Build tier DROPPED by user decision (builds use host resources; `-N` = runtime CAN-bus count). **Two WSL2 host crashes root-caused+fixed** (stdlib `_⊔_` value-linear under MAlonzo → `_⊔′_`; the leak) → [[feedback_value_linear_stdlib_cost]]. Mutation-gate lessons: a mutmut-hostile new test breaks the Python BASELINE (needs `--ignore`); a new C++ index-boundary loop over `string_view` yields an equivalent `<→<=` mutant (prefer `find_*_of`). Detail: CHANGELOG + git #229/#232/#233 + `memory/project_k1_rts_ssot.md`.

**⛩️ GEOMETRY REFUSE-AT-ENTRY ✅ MERGED 2026-07-21 (#222 `eba7b8bc`; J.1+E.7+E.8 closed — the E.3 follow-ups arc, BREAKING JSON wire).** The deep analysis surfaced real defects behind the innocuous backlog items (cross-surface crash: kernel-legal full-frame FD signals crashed every binding's decoder · false-refusal of textbook Motorola layouts · broken closure under emission · a second silent-rewrite channel in the BE conversion floor · clamp-position-dependent error classes). Shipped: **frame-capacity bounds** (the DLC decides classic vs FD; shared decider family `DBC.Decidable.SignalGeometry` consumed by entry gates, validator arms, AND checker — the form-skews can no longer be expressed) · **refuse-at-entry both routes/channels** (mod clamps + monus relocation retire; typed errors name SUBMITTED values; negative geometry gets a truthful `parse_non_natural_field`) · **BE no-wrap re-aimed pre-conversion** (Motorola layouts load; kernel closed under its own emission, regression-tested) · **E.7 = arms kept + machine-checked deadness theorem** (`DBC.Properties.GeometryGateDeadness`) · **E.8 resolved by consumption** (the re-aimed gate is `convertStartBit-roundtrip`'s first consumer). Wire codes per the addition/removal protocol (geometry refusals added; superseded codes + `big_endian_msb_layout` removed); binding decoders accept full-frame FD lengths. The battery caught a real stage-2 helper bug (payload bytes passed as DLC code — coincidence-correct up to classic CAN). Detail: CHANGELOG + git #222.

**🔬 E.3 tightness + validator mirrors ✅ MERGED 2026-07-20 (#218-#220).** Proven tightness verdicts in the `WellFormedCheck.agda` header (witness oracle = always-strict `format_dbc_text`); binding docs state the guarantee level; CHECK 24/25 name the round-trip-fatal mux shapes at validate/load on shared deciders (`WellFormedCheck/Foundations` SSOT). Detail: CHANGELOG + the module header + git #218-#220 + `memory/project_e3_tightness.md`.

**📦 Distribution hardening ✅ COMPLETE 2026-07-19 (#213-#216; Phase 6 item 1 closed).** Always-on dist-staging gate · SBOM bills bundled binding sources with a coverage gate · bundle validation executes the installers' own recipes (gates publish; weekly schedule workflow, acceptance green) · nfpm `.deb`/`.rpm` (payload byte-identity proven) + keyless-signed GHCR image (BuildKit verify stages). First tag-triggered release = the remaining full-path acceptance test; then the user's one-time GHCR visibility flip (RELEASE.md). Detail: PROJECT_STATUS § Phase 6 + CHANGELOG + git #213-#216.

**🔒 Wire-code SSOT + completeness gates ✅ MERGED 2026-07-19 (#211; G.3+H.2).** `docs/WIRE_CODES.yaml` pins both kernel wire vocabularies; `check-wire-codes` anchors YAML↔formatter arms; per-binding completeness tests anchor every binding; Rust `IssueCode`/`Error` `#[non_exhaustive]` (BREAKING Rust-only). **USER RULE 2026-07-19**: prose about code carries no hard-coded counts and no line-number references — describe structure qualitatively or name the SSOT; measurements, spec constants, versions/dates, and machine-re-derived numbers keep their digits (`memory/feedback_self_referential_count_drift.md` + AGENTS/docs.md cat 14). Detail: CHANGELOG + git #211.

**🏷️ v4.0.0 RELEASED 2026-07-17 — self-contained multi-binding distribution bundle (#198 keyless · #200 env constructors · #201 payload `0bb7f2ac` · #204 prepare-v4.0.0 `7795008f` → tag `v4.0.0`).** MAJOR (breaking `format_dbc_text` ×4). Published + real-downloader verified: published tarball `sha256 -c` OK + `cosign verify-blob` (keyless, vs `release.yml@refs/tags/v4.0.0`) = Verified OK; then install.sh → `pip install --target` → `source env.sh` → ran a full LTL verification (DBC + 3 props + 2 frames) on a clean py3.14. A `v*` tag → `shake dist` → **keyless-sign** (Sigstore / GitHub Actions ambient OIDC — NO key/passphrase in CI) → **self-verify vs the workflow OIDC identity, publish gated** → DRAFT Release. `shake dist` now ALSO bundles all four language wrappers (`bindings/{python,cpp,go,rust}`, library files via `git archive HEAD` — no tests, no `go.work`) + `env.sh`/`env.fish` (self-locating, ABSOLUTE `ALETHEIA_LIB`) + `install.sh`/`install.fish` (print per-shell/per-lang wiring, never edit an rc file) + `LICENSE`; all four bindings read `ALETHEIA_LIB` (Go `NewFFIBackendFromEnv` / C++ `make_ffi_backend_from_env` added #200). Gated by a dist **self-check** (proven teeth) + a release-workflow **functional smoke**. **NOT pip** (`--bignum=native` not needed). 2 adversarial rounds + 6 Copilot + 1 self-review fix. Detail: PROJECT_STATUS § Phase 6 + `memory/project_r26_product_gaps.md` + git #198/#200/#201/#204.

**Mid-July arcs ✅ CLOSED 2026-07-16** (one-line; detail at pointers): agent-memory-citation gate #195/#196 (`check_no_memory_citations.py`; source AND docs gated, AI-infra exempt — [[feedback_no_memory_citations_in_source]]) · gate-soundness + iwyu + comment-quality #190–#194 (USER RULE *a gate that can't fail on an issue HAS A BUG* → [[feedback_gate_pass_is_absence_of_output]]; iwyu validated vs the recompile oracle → [[feedback_fixture_matrix_coverage_is_the_gate]]; `DBC.Properties`→`DBC.Decidable` split). Detail: PROJECT_STATUS + CHANGELOG + git #190–#196.

**✅ E.2 CLOSED 2026-07-18 (route (b) shipped #181/#183/#187; item removed).** `format_dbc_text` returns `.dbc` text that provably re-parses to the input DBC, or a typed `handler_text_roundtrip_failed` refusal — machine-checked (`formatDBCTextResult-sound`), ×4 bindings. Universal `validity ⇒ WellFormedTextDBCAgg` is structurally impossible (warning-class walls by design) — the terminal form is reached; the why lives in the `Properties.WellFormedFromValidity` module header. Strategy docs deleted; the design plan lives on as `EXTENDED_MUX_DESIGN.md` (A.1/A.3). [[project_e2_reexamination]].

**Early-July arcs ✅ CLOSED** (one-line; detail at pointers): v3.0.0 #171 + stale-dist fix ([[feedback_release_stale_dist_tree]]) · merge-queue arc #157-#168 ([[project_r25_binding_review]]) · byte-exact parser positions + shake-install freshness gate #155/#156 ([[project_v2_parser_position_design]]) · validate first-touch #147-#153 ([[project_validate_cli_first_touch]] + [[project_cli_integration_harness]]) · merge-queue day + flake hardening #143-#145/#125-#129 ([[feedback_nonfatal_not_silent]]) · decoder-reject sweep #138-#142 ([[project_xbinding_decoder_reject_audit]]) · float-principle sweep #130-#136 ([[project_log_rational_values]]).

**Standing way of working** (still current): user GPG-signs all commits via the `.commands-to-run.sh` dribble; attribution = the active Claude model's `Co-Authored-By` + the Claude Code PR footer (`memory/feedback_commit_workflow_signed.md`); pipeline-PRs; ultracode.

**June-era arcs ✅ CLOSED** (each one-line; full detail at its pointer): CI-speed + proof-gate exhaustiveness #122/#123 (`memory/project_ci_speed_optimization.md`) · 4-binding API review closed 2026-07-07, shipped across #80-164 (`memory/project_r25_binding_review.md`) · cancellation-test robustness ×4 #85-87 (CANCELLATION.md) · lazy batch frame send Go/C++/Rust #79 (CHANGELOG) · mutation lane repaired+cached+required #71/#72 (`memory/project_mutation_to_zero.md`) · Rust parity + review #53-77 (`memory/project_rust_parity_r1.md`) · Go check-builder float-error fix #61, BREAKING Go (CHANGELOG).

**🧾 CI-PROGRAM CLOSE-OUT ✅ #51** (2026-06-17) — `check_changelog.py` extended to build/CI/tooling paths + the incremental-build doc pass. Detail: `memory/project_ci_speed_optimization.md`.

**⚡ RUNNER-CACHING + DEPENDABOT BATCH ✅** (2026-06-17, `ad3ed8c`) — run_ci split, build-tree cache (~384s→~23s), ccache, staleness gates; warm runner ≈13min; then Dependabot #41-46. Detail: `memory/project_ci_speed_optimization.md` + `memory/feedback_watch_registration_race.md`.

**⚡ INCREMENTAL + STALENESS-SAFE BUILD ✅ MERGED 2026-06-15** (PR #37 `e80a101`) — `.so` now builds incrementally (no-op ~0.1s, one-module ~12s): the Shake `.so` rule depends on `.agda` SOURCES + `aletheia.cabal` lists every MAlonzo module (`-Werror=missing-home-modules` drift gate); + `check_build_incremental` staleness gate, `AgdaVersion` oracle, `iwyu` target. Now fully documented in BUILDING.md/CI_LOCAL.md (G.3). Detail: `memory/project_build_so_idempotency.md` (RESOLVED), `memory/feedback_no_git_checkout_in_revert_traps.md`.

**🦀 RUST TYPED BINDING ✅ 2026-06-14** — typed client + the fourth FEATURE_MATRIX column/parity gate; foundation for the Rust parity work (see that entry). Detail: PROJECT_STATUS § Phase 6.

**🪞 GO/C++ MOCK FIDELITY + 🧹 DEAD JSON-STREAMING PRUNE ✅** (2026-06-14) — mocks record `<binary:OP>` sentinels matching Python (fabricated JSON dropped); the 5 test-only JSON streaming-command mirrors + dead binding serializers removed (binary FFI retained). Detail: PROJECT_STATUS.

**🔒 SINGLE-VENV ENFORCEMENT ✅** (2026-06-14) — `tools/check_venv_convention.py` gate: exactly one venv at `python/.venv`; caught a real `run_all.sh` bug. Rule: AGENTS.md § Universal Rules; lesson `memory/feedback_single_venv.md`.

**🔎 FEATURE_MATRIX SEMANTICS ✅ #23** — the structural gate checks entry-resolves + reason-non-empty only, never status correctness; C++ `mock_backend`→`planned` (H.1). Lesson: `memory/feedback_feature_matrix_status_semantics.md`.

**🟢 PHASE 6 — CLI PARITY (C++/Go) ✅ #21** — Go `go/cmd/aletheia` + C++ `aletheia::run_cli` (`aletheia-cli`): 5 subcommands dispatching to the verified core; FEATURE_MATRIX `cli` ×3; real-FFI tests. `check` deferred (needs `can_log_reader`). Lessons: `memory/feedback_command_dribble_file.md`, `memory/feedback_verify_actions_before_claiming.md`.

**🔐 RELEASE-SIGNING + ACCESS HARDENING ✅ 2026-06-12** (PR #20) — cosign key rotated to passphrase-protected (v2.0.0 re-signed; verification anchors on the published SHA-256 fingerprint); write-collaborators removed; `v*` tag creation admin-only + `required_signatures` on `main`; GPG signing (key exp **2028-06-10**, renew before). GitHub can't enforce signed tag *objects* — signed tags are a practice. Detail: `memory/project_release_signing_hardening.md`.

**🏷️ 2.0.0 RELEASED 2026-06-11 (#18, tag `v2.0.0`)** — clang-22 adoption (CI + Mull-22 + ubsan); benchmark PR regression gate; CPP_API/GO_API references; first signed Release (cosign + Rekor). CHANGELOG `[2.0.0]` (21 BREAKING since v1.1.1). Lesson: `memory/feedback_no_shebang_in_tools.md`.

**A.2 — `BO_TX_BU_` message senders ✅ DONE 2026-06-11** — the verified DBC text round-trip now carries message senders (`BO_TX_BU_` as an 8th synthesized section, VAL_ analogue); `WellFormedTextDBCAgg` is strictly weaker; `parse_dbc_text` now attaches transmitters instead of dropping. Module count 269→**273**. (E.2 stays HOLD at 5/9.) Full detail + the incremental commit map + the "never `rewrite` over a parser-bearing goal" lesson: `memory/project_a2_botxbu_senders.md`, `memory/feedback_no_rewrite_over_parser_goal.md`.

**`ci/pr-heavy-lanes` ✅ MERGED** (PR #16, 2026-06-10) — the heavy-lanes workflow (parallel repro/stability/mutation; repro REQUIRED, others ADVISORY) + the mutation-to-zero campaign (C++ 0 / Python 215→1 documented-equivalent / Go 0; baselines in `docs/MUTATION_BENCH.yaml`; no defenses deleted for the metric). Detail: `memory/project_mutation_to_zero.md`, `memory/feedback_mutation_no_defense_removal.md`.

**`ci-speed` ✅ MERGED** (PR #7, 2026-06-09) — the fast-gate program: warm `check-properties` IS the proof gate (~13×), `tools/iwyu.py` is the `.agdai` import gate, tree-wide lint enforcement (ruff ALL + pylint 10 + basedpyright 0/0/0), renderer-faithfulness proofs. Module count 266. Detail: `memory/project_ci_speed_optimization.md`, `memory/project_agda_iwyu.md`.

**Branch & PR hygiene ✅ ENFORCED** — `.github/workflows/pr-full-ci.yml` runs `tools/run_ci.py` (all gates) on every `pull_request` + `push:main`; the `main` ruleset now **requires** `tools/run_ci.py (all gates)` (2026-06-10) **and `mutation testing`** (2026-06-20, #72 — drift gate, merge-blocking).  C++ builds with **Clang 22** (the supported toolchain — see [BUILDING.md § Toolchain support policy](docs/development/BUILDING.md#toolchain-support-policy)), enforced in `cpp/CMakeLists.txt`.  Detail: `docs/development/BRANCH_PR_HYGIENE.md`, `memory/project_cpp_compilers.md`.

**Post-merge cleanup** (2026-06-10): `docs/development/DEFERRED_ITEMS.md` created — the open backlog lives there (E.2 closed 2026-07-18 — route (b) shipped, item removed; lossless emission lives in A.1/A.3 with `EXTENDED_MUX_DESIGN.md` as the retained design plan; the rest HOLD/CAN'T or parked by prior user decision).

**Phase 6 — CLI parity (C++/Go) ✅ done 2026-06-12** (the quick-wins track; see top). Remaining Phase 6 candidates (not started): Rust/Haskell bindings (Haskell native; Rust via `.so`), python-can replacement (`can_log_reader`), GHC native bignum, SOME/IP.

**Standard gates** (all run by `tools/run_ci.py`; the full ordered sequence is [AGENTS.md § Step 4](AGENTS.md#step-4-implement-and-verify) — the canonical source): Agda `build` + the proof gates (`check-properties` and siblings), Python `pytest`, Go `go test -race`, C++ `ctest` (Clang 22), tree-wide lint (ruff / pylint / basedpyright), IWYU (`tools/iwyu.py`), GHA meta (actionlint / pin / permission checks), and SPDX headers.

## Prior work (closed) — see PROJECT_STATUS.md for narratives

- **VAL_ promotion** ✅ 2026-05-08 — VAL_ value descriptions promoted to `DBCSignal.valueDescriptions`; bundled commit. Detail: `memory/project_track_e_val_promotion.md`.
- **Doc-example harness** ✅ 2026-05-04 — cross-binding doc-example harness (Python `pytest --markdown-docs` + Go `TestDocExamples` + C++ Catch2).
- **Cancellation contract** ✅ 2026-05-03 — bound across all 3 bindings. Detail: `memory/project_track_c_cancellation.md`.
- **Universal DBC roundtrip** ✅ 2026-05-03 — universal roundtrip + bindings + cantools dropped (LGPL contingency realised). Detail: `memory/project_b3e_parsedbctext.md`.
- **Universal roundtrip target** — `∀ d → WellFormedDBC d → parseText (formatText d) ≡ inj₂ d` proven in `Substrate/Unsafe.agda` (sole axiom consumer; co-located by Unsafe-module policy). Detail: `memory/project_b3d_universal_proof.md`.

## Format DSL toolkit (`DBC/TextParser/Format.agda`)

- **Core constructors**: `literal` / `ident` / `nat` / `stringLit` / `pair` / `iso` / `many` / `refined` / `altSum` / `withPrefix`.
- **Whitespace family** (each with distinct parser permissiveness — see `feedback_format_dsl_ws_family_discipline.md`): `ws` / `wsOpt` / `wsCanonOne` / `wsCanonTab` / `withWS` / `withWSOpt` / `withWSCanonOne` / `withWSCanonTab` / `withWSAfter`.
- **Refinement carriers**: `decRat` / `intDecRat` / `natDecRat`.
- **Sugar**: `discardFmt` (wire-only fields) / `nonNewlineRun` (opaque-tail consumer) / `newlineFmt` (LF/CRLF).
- **Cycle-break pattern**: when a Format module would close a cycle, extract the cycle-relevant subset to a `Foundations.agda` submodule.

## Performance baseline

Current profile (JSON-mirror runtime impact retained from `320c5a9`): Stream LTL +12-38% across bindings (Bool fast path); Signal Extraction -2-9% / Frame Building -1-7% (structural cost). All later Format DSL work + the VAL_ promotion are proof-only and runtime-neutral on the streaming hot path. Baselines NOT refreshed per user "wait and see" 2026-04-28; COMPILE-pragma escape hatch deferred (requires explicit user approval per `feedback_no_suppression_without_approval`).

**Cross-binding parity**: tracked in [docs/FEATURE_MATRIX.yaml](docs/FEATURE_MATRIX.yaml) (the parity plan is complete). Every `DBC` / `DBCSignal` / `DBCMessage` field — Tier 1 + Tier 2 metadata, signal receivers, message senders, VAL_ value descriptions — ships across all 3 bindings, with FEATURE_MATRIX rows (`dbc_metadata_tier1` / `_tier2` / `dbc_signal_receivers` / `dbc_message_senders` / `dbc_signal_value_descriptions` / `dbc_text_format`) + per-binding parity tests + CHECK 23 `unknown_value_description_target` IssueCode mirror. Check-fidelity coverage, the cancellation contract, the DBC text round-trip, and the doc-example harness are likewise all complete (2026-05-07).
