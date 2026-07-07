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

**Size budget** — after the sweep, check BOTH authoritative doc surfaces and reduce any that is over its limit:
- **CLAUDE.md**: `wc -c CLAUDE.md`, limit **40.0 kB**. If over, compress in the same UPD commit — push per-cluster narrative detail into the appropriate `memory/project_*.md` file (e.g. `project_review_round20.md`) and replace with a one-line index pointer, mirroring how prior rounds compressed (e.g. R6-B8.2's `970f704` compression of Current Session Progress). The compression IS doc-state sync; do not split into a separate commit.
- **MEMORY.md**: `wc -l ~/.claude/projects/-home-nicolas-dev-agda-aletheia/memory/MEMORY.md` (the agent store, NOT the repo root), limit **200 lines**. If over, compress in-place — move detail from any over-long or multi-line index entry into its `memory/*.md` topic file and collapse the pointer to a single ≤200-char line; merge or drop stale/duplicate/superseded pointers. MEMORY.md lives in the agent memory store under `~/.claude/` (**outside this repo**), so its reduction is an in-place memory edit, NOT part of the UPD git commit.

**UPD is a doc-state sync only.** The resulting commit must contain ONLY doc-sweep edits. Pre-existing uncommitted work (refactors, structural cleanups, prior tasks) goes in its own commit at task completion, never bundled into UPD. See `memory/feedback_upd_scope.md`. Apply the 2-question pre-commit gate (`feedback_pre_commit_scope_check.md`) before committing the doc sweep.

**UPD frequency rule (token-efficiency).** Run UPD **once per round close**, or once per coherent cluster-series close — not after every single cluster. R22 ran 19 UPDs across 65 commits (29% of all commits were doc syncs); each UPD re-loads CLAUDE.md (~40 KB), so 19 UPDs amount to ~760 KB of CLAUDE re-reads alone. The right cadence: small-cluster work (e.g. each `b25` batch) updates `.session-state.md` (gitignored — no token cost to other sessions) during the work, then a single UPD at the end syncs CLAUDE.md / MEMORY.md / PROJECT_STATUS.md. Exception: when a cluster surfaces a new durable rule (a new `memory/feedback_*.md` worth indexing) AND subsequent work depends on that rule being indexed, that single rule can warrant its own UPD. When in doubt, defer the UPD to the next natural rest-point.

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

278 total modules (`cabal run shake -- count-modules`):
- **273**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer — co-located here to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

277 of 278 modules use `--safe`. No modules require `--sized-types`. The per-commit module-count genealogy (which split/extraction added each module across A.2, Path A.4, Tracks D/E, rounds R18–R23, and the #107 dual-route factoring's `Handlers.LoadDBC`) lives in [PROJECT_STATUS.md](PROJECT_STATUS.md) and the `memory/project_*.md` round files — not duplicated here.

## Common Commands

See [Building Guide](docs/development/BUILDING.md). Quick reference:

```bash
# Type-check a single module
cd src && agda +RTS -N32 -M16G -RTS Aletheia/YourModule.agda

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
2. Type-check fast: `cd src && agda +RTS -N32 -M16G -RTS Aletheia/Parser/Combinators.agda`.
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

Wraps `libaletheia-ffi.so` via `dlopen`. `IBackend` interface; `MockBackend` for tests. Strong types (`std::byte`, validated newtypes, `std::expected`). Custom `Logger` (~90L, callback-based, 16 event types matching Go's slog, zero-cost when null). RTS cores via `make_ffi_backend(path, rts_cores)` (default 1, once-per-process with mismatch warning). C++23, **Clang 22** (the supported toolchain — see [BUILDING.md § Toolchain support policy](docs/development/BUILDING.md#toolchain-support-policy)); needs a libstdc++/libc++ with C++23 (`<expected>`). Style: `.clang-format` + `.clang-tidy`. Inventory: [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics).

### Go Binding (`go/`)

Wraps `libaletheia-ffi.so` via cgo + dlopen. `Backend` / `MockBackend` / `FFIBackend` (with C trampolines). Strong types (`[]byte` payload + DLC validation, validated CAN ID / DLC newtypes, sealed CanID/Predicate/Formula interfaces). `slog` via `WithLogger` option (16 event types); `ViolationEnrichment.CoreReason` carries Agda core reason strings. RTS cores via `WithRTSCores` functional option. `Client` is goroutine-safe via a 1-deep channel-token semaphore (`lockCh chan struct{}`) chosen over `sync.Mutex` so that `ctx`-aware `TryLock` cancellation works correctly (see `docs/architecture/CANCELLATION.md`); double-close safe; GHC RTS init thread-pinned (`LockOSThread`). Optional `go/excel/` is a separate Go module pulling `xuri/excelize`; depend on it only for the Excel loader. Inventory: [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics).

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

[PROJECT_STATUS.md](PROJECT_STATUS.md). Current state: Phase 5.1 complete (binary FFI 4.3× CAN 2.0B / 9.1× CAN-FD; CAN-FD; C++/Go bindings; cross-language benchmarks; four-tier check interface with full parity); post-R17 parity-plan Tracks A–E all complete (matrix gates / DBC text parser / cancellation / doc harness / VAL_ promotion). **No active phase**; Phase 6 (Extensions & New Protocols — CLI parity stretch + Rust/Haskell bindings (Haskell native; Rust via .so) + python-can replacement + GHC native bignum + SOME/IP) is the candidate next track, goal-set pinned 2026-05-07 but not started.

---

## Notes for newcomers

Start with the [Project Pitch](docs/PITCH.md) for context.

**Operational pitfalls** (most are caught by build/lint, but easy to trip on first time):
- `Dec`-valued predicates on the streaming hot path: MAlonzo allocates per call. Use `Bool`-valued fast path + equivalence lemma (`extractSignalCoreFast`).
- Fuel-based parser combinators: structural recursion on `length input` only.
- Type-checking without `+RTS -N32 -RTS`: large modules time out past 120s.
- Running tools from the repo root: `pytest` / `basedpyright` / `pylint` need `cd python` first (config picks up nearest `pyproject.toml`).

**Key terms used elsewhere in this file:**
- **"Phase" (capital P) is reserved.** It denotes a **whole-project phase only** — Phase 1 … Phase 6 (see [PROJECT_STATUS.md](PROJECT_STATUS.md) § Project Phases). **Never call the sub-units of any other plan "phases"** — it conflates them with project phases and causes confusion. For the Rust binding's incremental deliverables use **"slice"** (the established term: "tracer-bullet slice", "a later Rust slice"); for other plans use "cluster" / "stage" / "step" / "track". Worked example: [docs/development/RUST_PARITY_PLAN.md](docs/development/RUST_PARITY_PLAN.md) organizes its work into *slices*, not phases. (Convention pinned 2026-06-14 at user request.)
- **MAlonzo**: Agda's Haskell backend. `agda --compile` produces a `MAlonzo/` directory of generated `.hs` files; the Cabal package and FFI shared library are built on top. Function names get mangled.
- **`Dec A`**: A type expressing decidability (`yes (a : A) ⊎ no (¬ A)`). Carries a *proof object* at runtime — that's why it allocates on hot paths.
- **`memory/<name>.md`**: a pointer to Claude Code's agent memory store (under `~/.claude/`, **outside this repository**) — written for the agent, not a repo-relative link, so it will not resolve in a repo checkout. The same convention appears in several docs (AGENTS.md, PROJECT_STATUS.md, …). Documented here as an explicit convention 2026-06-12 — it had accreted unratified, not by deliberate decision.

**Code style**: per-language conventions live in [AGENTS.md](AGENTS.md). Don't duplicate here.

**Pre-commit minimum** (doc-only changes): `agda +RTS -N32 -M16G -RTS src/Aletheia/Main.agda` → `cabal run shake -- build` → relevant binding tests.

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

**🔀 MERGE-QUEUE ARC ✅ 2026-07-06/07 (#157–#164) — r25 CLOSED (#106/#107 + PR D/E)** — eight PRs merged serially (`main` ruleset `strict:true` → each merge BEHINDs the next; choreography `gh pr merge --squash --auto` + `update-branch`, ~26 min CI/cycle; docs-only diffs make the mutation lane diff-scope to ~4 min). **#157/#161** UPD doc-syncs. **#158 CLI single-parse (#106 ✅)**: every CLI parses a DBC ONCE (Python `.dbc` via `parse_dbc_text`; redundant ValidateDBC round-trip dropped ×3; Excel parse-status checked; `run_checks` gains `client=`). **#159 kernel dual-route factor + C2 (#107 ✅)**: new leaf `Protocol/Handlers/LoadDBC.agda` = the single field-tagged bound cascade + validate-and-load epilogue shared by `parseDBC`/`parseDBCText` (text-parser-free closure keeps Handlers.agda under the 16 GiB cap; modules 277→**278**); C2 = `validateDBC` runs the cascade → typed `input_bound_exceeded`; Python lifts via SSOT `lift_input_bound_exceeded`. Mutation lane caught 6 `validate_dbc` survivors → 2 correlated-guard equivalents **designed out** by typed extraction + 4 killed by an `err.code` assert ([[feedback_unkillable_mutant_is_design_signal]]). **#160 mutation-cache hygiene**: `run_python` erases `python/mutants/` before each run (mutmut invalidates on SOURCE but NOT test changes → 20 phantom survivors on a merged tree; local-only, CI always fresh) → [[feedback_mutation_cache_hygiene]]. **#162 CHANGELOG normalized** to Keep-a-Changelog one-header-per-category (accreted per-arc repeats collapsed; script-verified 1682 lines multiset-identical) → [[feedback_changelog_one_header_per_category]]. **#163 PR D (#101 ✅) EOS extract-once ×4**: `end_stream` enrichment P×F→extract-once, uniform in all four bindings (union-empty skip + early-break; Rust pin 2→1). Adversarial review 15 findings ALL fixed — Go frame-sort bug (extended-flag bit-32 dominated the sort → `(canID,extended)`), a vacuous Python count test, first-frame-wins undiscriminated ×4 (probe-verified). Collectors unified to kernel-SSOT pass-through (Python's empty-name filter removed — kernel `parse_invalid_identifier` is the validator). **#164 PR E (#102 ✅) Rust FFI symbol cache**: `Symbols` table resolves all 16 exports once (`Symbol<'static>` on the process-lifetime `Library`); `send_frame` 2 dlsym→0 (~+4.8%); non-latching (load outside `get_or_init`; export-less lib fail-fasts but stays loaded — doc'd). Verify round 7 findings incl. a CHANGELOG bullet-beheading ([[feedback_reread_structural_edits]] — struck twice this arc). **r25 binding-review program CLOSED.** Process rules earned: auto-merge fires on green regardless of review threads → poll Copilot immediately + `--disable-auto` if a fix is needed ([[feedback_pr_open_protocol]]); a "clean" auto-merge can be structurally wrong; rebuild+reinstall after every branch switch. **Next: #108 (MockBackend error-on-exhaustion ×4).** Detail: PROJECT_STATUS head + CHANGELOG + git #157–#164.

**🎯 V2b BYTE-EXACT PARSER POSITIONS ✅ + SHAKE-INSTALL / FRESHNESS GATE ✅ 2026-07-05 (#155/#156)** — task #105 ✅: furthest-failure positions on the E2 watermark encoding (`Parser A = Position → List Char → Position × Maybe (ParseResult A)`); ~100 proof modules restated at the `proj₂` outcome level, zero failures; bindings green ZERO edits (+ the byte-exact CLI pin `midfile_bad` L40 C22); DBC-text cold +3-5%, hot path untouched; modules stay 277. **#155**: `shake install` repaired (dead since 2026-02-08) + the deployed-kernel freshness gate (`check_install_freshness.py`). Rule earned: [[feedback_conflict_blocks_pull_request_ci]]. Detail: PROJECT_STATUS + [[project_v2_parser_position_design]] + CHANGELOG + git #155/#156.

**🎯 VALIDATE FIRST-TOUCH ✅ + V2a ✅ 2026-07-04/05 (#147–#153)** — `aletheia validate` on a broken DBC lists the full issue set (errors AND warnings — were dropped) and exits 1 ×3 CLIs, locked by a 40-test cross-CLI harness (`docs/CLI_SCENARIOS.yaml` + `test_cli_parity.py`). Kernel #150: structured `issues` envelope + positioned parse errors + typed `AttributeRefinementFailed` cause+name. Bindings #152: 4 typed validation errors (code-gated lift; Python via the SSOT helper). #147-#149 closed r25 B6-logging/B8. #153 V2a: Position+CharClass leaf modules (275→277). Rules earned: [[feedback_stacked_pr_retarget_before_parent_merge]] (cost #151), [[feedback_never_unsigned_commits]]. Detail: [[project_validate_cli_first_touch]] + [[project_cli_integration_harness]] + git #147-#153.

**🔁 MERGE-QUEUE DAY + FLAKE HARDENING ✅ 2026-07-02/03 (#143-145 + #125-129)** — queue drained (B7 comment-truth #144; B6e residual #125 rescued — "task completed" ≠ "on main"; Dependabot ×4) + #145 flake hardening (retry-once both advisory lanes + FLAKE-RETRY tally; thresholds unchanged). Lesson: [[feedback_nonfatal_not_silent]]. Detail: [[project_python_stability_jitter_watch]] + memory/project_r25_binding_review.md + CHANGELOG + git #143-145.

**🧪 CROSS-BINDING DECODER-REJECT SWEEP ✅ #138-142 (2026-07-02)** — Py/C++/Rust reject-class audit; the Marshal.hs show-as-JSON envelope bug fixed at the SSOT; Rust typed `input_bound_exceeded` lift + its missing matrix row (43 rows). Lessons: [[feedback_matrix_row_or_invisible]]; read-audit=hypothesis, tool-measure=evidence. Detail: memory/project_xbinding_decoder_reject_audit.md + git #138-142.

**🎯 FLOAT-PRINCIPLE SWEEP ✅ #130-136 (2026-07-01)** — exact rational everywhere, float only at print-out (timestamp input the lone Phase 6 exception); no lossy user-facing rational render remains. Detail: memory/project_r25_binding_review.md + memory/project_log_rational_values.md + git #130-136.

**⚡ CI-SPEED + PROOF-GATE EXHAUSTIVENESS ✅ #122/#123** (2026-06-29) — throughput lane ~12→~4.5min (build-tree cache now captures the cabal foreign-lib `haskell-shim/dist-newstyle`; ghcup cache dropped = 6.2GB symlink) + a drift-proof `check-proof-coverage` gate (`closure(proofModules)∪closure(build)` covers every `src/**.agda`). Detail: `memory/project_ci_speed_optimization.md` + CHANGELOG + git #122/#123.

**🔬 r25 4-BINDING API REVIEW ✅ CLOSED 2026-07-07** — 65 findings across Py/Go/C++/Rust (spec `.archive/reviews/r25/FINAL_report.md`), shipped #80-164: B1-B8 + the B6 decimal-SSOT arc + the float-principle sweep + PR D (EOS reshape #163) + PR E (Rust symbol cache #164). Detail: `memory/project_r25_binding_review.md` + `memory/project_mutation_to_zero.md` + CHANGELOG + git. **Standing way of working** (still current): attribution `Co-Authored-By: Claude Opus 4.8` + PR Claude Code footer (`memory/feedback_commit_workflow_signed.md`), single-slot dribble (user GPG-signs commits), Lever B pipeline-PRs, ultracode.

**🛡️ CANCELLATION-TEST ROBUSTNESS (4 bindings) ✅ #85-87** — Rust async backend DI seam (`build_async_with_backend`) + deterministic in-flight cancel test; C++/Go release-the-worker-on-unwind so a parked-worker teardown can't deadlock/terminate. Detail: CHANGELOG + CANCELLATION.md + git #85-87.

**🪺 LAZY BATCH FRAME SEND (Go/C++/Rust) ✅ #79** (2026-06-22) — lazy/streaming batch-send for the 3 non-Python bindings (Go `iter.Seq2`, C++ `std::generator`, Rust `impl Iterator`/`impl Stream`); matrix now has zero `not_applicable` cells (rust 37/40). Rules earned: [[feedback_property_defined_task_acceptance]] + [[feedback_rust_verify_fmt_and_clippy]]. Detail: CHANGELOG + CANCELLATION.md §3.2-3.4 + git #79.

**🧬 MUTATION LANE REPAIRED + CACHED + REQUIRED ✅ 2026-06-20 (#71/#72)** — the advisory `mutation testing` lane was **crash-dead** (zero mutants since #51 — a baseline-COLLECTION failure, NOT survivors); #71 fixed it (`--ignore`/`--deselect` + mutmut-3.6 keys + always-on `check_mutation_setup.py` gate → baseline 827/1/828), #72 cached it (push:[main] seeds Mull+build-tree caches; ~33→~22min) and made `mutation testing` a `main`-ruleset **required** check (gh `PUT`). Detail: `memory/project_mutation_to_zero.md` + CHANGELOG + git #71/#72.

**🦀 RUST PARITY R1–R5 ✅ + r24 REVIEW ✅ (#53-77, rust 37/40)** — functional parity with Py/Go/C++ (typed DBC, frame build/update+mux, check tier, logging/enrichment, runtime-agnostic `AsyncClient`, open `Backend` DI-seam + `Clone` `MockBackend`); only Phase 6 host rows remain. r24 multi-agent review (#77): 10 fixed, 2 BREAKING. Earned the two cross-binding-review rules now in AGENTS.md (read ALL peers; consistency≠correctness). Detail: `memory/project_rust_parity_r1.md` + `RUST_PARITY_PLAN.md` + git #53–77.

**🐹 GO CHECK-BUILDER FLOAT-ERROR FIX ✅ #61** (2026-06-18) — Go check builders silently clamped bad floats to `0/1` (peers raise/throw); now uniform `(CheckResult, error)`; BREAKING (Go). Detail: CHANGELOG + git #61.

**🧾 G.x CI-PROGRAM CLOSE-OUT ✅ #51** (2026-06-17) — G.2 `check_changelog.py` extends to build/CI/tooling paths + G.3 the incremental-build doc pass. Detail: `memory/project_ci_speed_optimization.md`.

**⚡ RUNNER-CACHING + DEPENDABOT BATCH ✅** (2026-06-17, `ad3ed8c`) — run_ci split (G.4), build-tree cache (~384s→~23s), ccache, staleness gates; warm runner ≈13min; then Dependabot #41-46. Detail: `memory/project_ci_speed_optimization.md` + `memory/feedback_watch_registration_race.md`.

**⚡ INCREMENTAL + STALENESS-SAFE BUILD ✅ MERGED 2026-06-15** (PR #37 `e80a101`) — `.so` now builds incrementally (no-op ~0.1s, one-module ~12s): the Shake `.so` rule depends on `.agda` SOURCES + `aletheia.cabal` lists all 433 MAlonzo modules (`-Werror=missing-home-modules` drift gate); + `check_build_incremental` staleness gate, `AgdaVersion` oracle, `iwyu` target. Now fully documented in BUILDING.md/CI_LOCAL.md (G.3). Detail: `memory/project_build_so_idempotency.md` (RESOLVED), `memory/feedback_no_git_checkout_in_revert_traps.md`.

**🦀 RUST TYPED BINDING ✅ 2026-06-14** — tracer→typed client + the fourth FEATURE_MATRIX column/parity gate; foundation for R1–R5 (see that entry). Detail: PROJECT_STATUS § Phase 6, `docs/development/RUST_PARITY_PLAN.md`.

**🪞 GO/C++ MOCK FIDELITY ✅** (2026-06-14) — mocks record `<binary:OP>` sentinels matching Python; fabricated JSON shapes dropped. Detail: PROJECT_STATUS.

**🧹 DEAD JSON-STREAMING PRUNE ✅** (2026-06-14, `2ea8ecf`) — the 5 test-only JSON streaming-command mirrors removed from the verified core + dead binding serializers; binary FFI retained; benchmark-neutral. Detail: PROJECT_STATUS.

**🔒 SINGLE-VENV ENFORCEMENT ✅** (2026-06-14) — `tools/check_venv_convention.py` gate: exactly one venv at `python/.venv`; caught a real `run_all.sh` bug. Rule: AGENTS.md § Universal Rules; lesson `memory/feedback_single_venv.md`.

**🔎 FEATURE_MATRIX SEMANTICS ✅ #23** — the structural gate checks entry-resolves + reason-non-empty only, never status correctness; C++ `mock_backend`→`planned` (H.1). Lesson: `memory/feedback_feature_matrix_status_semantics.md`.

**🟢 PHASE 6 — CLI PARITY (C++/Go) ✅ #21** — Go `go/cmd/aletheia` + C++ `aletheia::run_cli` (`aletheia-cli`): 5 subcommands dispatching to the verified core; FEATURE_MATRIX `cli` ×3; real-FFI tests. `check` deferred (needs `can_log_reader`). Lessons: `memory/feedback_command_dribble_file.md`, `memory/feedback_verify_actions_before_claiming.md`.

**🔐 RELEASE-SIGNING + ACCESS HARDENING ✅ 2026-06-12** (PR #20) — cosign key rotated to passphrase-protected (v2.0.0 re-signed; verification anchors on the published SHA-256 fingerprint); write-collaborators removed; `v*` tag creation admin-only + `required_signatures` on `main`; GPG signing (key exp **2028-06-10**, renew before). GitHub can't enforce signed tag *objects* — signed tags are a practice. Detail: `memory/project_release_signing_hardening.md`.

**🏷️ 2.0.0 RELEASED 2026-06-11 (#18, tag `v2.0.0`)** — clang-22 adoption (CI + Mull-22 + ubsan); benchmark PR regression gate; CPP_API/GO_API references; first signed Release (cosign + Rekor). CHANGELOG `[2.0.0]` (21 BREAKING since v1.1.1). Lesson: `memory/feedback_no_shebang_in_tools.md`.

**A.2 — `BO_TX_BU_` message senders ✅ DONE 2026-06-11** — the verified DBC text round-trip now carries message senders (`BO_TX_BU_` as an 8th synthesized section, VAL_ analogue); `WellFormedTextDBCAgg` is strictly weaker; `parse_dbc_text` now attaches transmitters instead of dropping. Module count 269→**273**. (E.2 stays HOLD at 5/9.) Full detail + the green-slice commit map + the "never `rewrite` over a parser-bearing goal" lesson: `memory/project_a2_botxbu_senders.md`, `memory/feedback_no_rewrite_over_parser_goal.md`.

**`ci/pr-heavy-lanes` ✅ MERGED** (PR #16, 2026-06-10) — the Phase-2 heavy-lanes workflow (parallel repro/stability/mutation; repro REQUIRED, others ADVISORY) + the mutation-to-zero campaign (C++ 0 / Python 215→1 documented-equivalent / Go 0; baselines in `docs/MUTATION_BENCH.yaml`; no defenses deleted for the metric). Detail: `memory/project_mutation_to_zero.md`, `memory/feedback_mutation_no_defense_removal.md`.

**`ci-speed` ✅ MERGED** (PR #7, 2026-06-09) — the post-R23 fast-gate program: warm `check-properties` IS the proof gate (~13×), `tools/iwyu.py` is the `.agdai` import gate, tree-wide lint enforcement (ruff ALL + pylint 10 + basedpyright 0/0/0), renderer-faithfulness proofs. Module count 266. Detail: `memory/project_ci_speed_optimization.md`, `memory/project_agda_iwyu.md`.

**Branch & PR hygiene ✅ ENFORCED** — `.github/workflows/pr-full-ci.yml` runs `tools/run_ci.py` (all gates) on every `pull_request` + `push:main`; the `main` ruleset now **requires** `tools/run_ci.py (all gates)` (2026-06-10) **and `mutation testing`** (2026-06-20, #72 — drift gate, merge-blocking).  C++ builds with **Clang 22** (the supported toolchain — see [BUILDING.md § Toolchain support policy](docs/development/BUILDING.md#toolchain-support-policy)), enforced in `cpp/CMakeLists.txt`.  Detail: `docs/development/BRANCH_PR_HYGIENE.md`, `memory/project_cpp_compilers.md`.

**Post-merge cleanup** (2026-06-10): `docs/development/DEFERRED_ITEMS.md` created — the open backlog lives there (A.2 since ✅ DONE; E.2 HOLD 5/9 on the parked `agda/e1-isidentstart-hspace-bridge` branch; the rest HOLD/CAN'T or parked by prior user decision).

**Phase 6 — CLI parity (C++/Go) ✅ done 2026-06-12** (the quick-wins track; see top). Remaining Phase 6 candidates (not started): Rust/Haskell bindings (Haskell native; Rust via `.so`), python-can replacement (`can_log_reader`), GHC native bignum, SOME/IP.

**Standard gates** (all run by `tools/run_ci.py`; the full ordered sequence is [AGENTS.md § Step 4](AGENTS.md#step-4-implement-and-verify) — the canonical source): Agda `build` + the proof gates (`check-properties` and siblings), Python `pytest`, Go `go test -race`, C++ `ctest` (Clang 22), tree-wide lint (ruff / pylint / basedpyright), IWYU (`tools/iwyu.py`), GHA meta (actionlint / pin / permission checks), and SPDX headers.

## Prior Tracks (closed) — see PROJECT_STATUS.md for narratives

- **Track E** ✅ 2026-05-08 — VAL_ promotion to `DBCSignal.valueDescriptions`; Plan-A bundled commit. Detail: `memory/project_track_e_val_promotion.md`.
- **Track D** ✅ 2026-05-04 — cross-binding doc-example harness (Python `pytest --markdown-docs` + Go `TestDocExamples` + C++ Catch2). Closed R17-DEF-6.
- **Track C** ✅ 2026-05-03 — cancellation contract bound across all 3 bindings. Detail: `memory/project_track_c_cancellation.md`.
- **Track B.3** ✅ 2026-05-03 — universal roundtrip + bindings + cantools dropped (LGPL contingency realised). Detail: `memory/project_b3e_parsedbctext.md`.
- **B.3.d universal target** — `∀ d → WellFormedDBC d → parseText (formatText d) ≡ inj₂ d` proven in `Substrate/Unsafe.agda` (sole axiom consumer; co-located by Unsafe-module policy). Detail: `memory/project_b3d_universal_proof.md`.

## Format DSL toolkit (`DBC/TextParser/Format.agda`)

- **Core constructors**: `literal` / `ident` / `nat` / `stringLit` / `pair` / `iso` / `many` / `refined` / `altSum` / `withPrefix`.
- **Whitespace family** (each with distinct parser permissiveness — see `feedback_format_dsl_ws_family_discipline.md`): `ws` / `wsOpt` / `wsCanonOne` / `wsCanonTab` / `withWS` / `withWSOpt` / `withWSCanonOne` / `withWSCanonTab` / `withWSAfter`.
- **Refinement carriers**: `decRat` / `intDecRat` / `natDecRat`.
- **Sugar**: `discardFmt` (wire-only fields) / `nonNewlineRun` (opaque-tail consumer) / `newlineFmt` (LF/CRLF).
- **Cycle-break pattern**: when a Format module would close a cycle, extract cycle-relevant subset to a `Foundations.agda` submodule (used at 3d.5.c-ε / 3d.5.d-3c-A).

## Performance baseline

Path A profile (post-3d.4 + JSON-mirror, runtime impact retained from `320c5a9`): Stream LTL +12-38% across bindings (Bool fast path); Signal Extraction -2-9% / Frame Building -1-7% (Path A structural cost). All 3d.5+ Format DSL work + Track E sub-phases are proof-only and runtime-neutral on the streaming hot path. Baselines NOT refreshed per user "wait and see" 2026-04-28; COMPILE-pragma escape hatch deferred (requires explicit user approval per `feedback_no_suppression_without_approval`).

**Cross-binding parity roadmap**: [docs/development/PARITY_PLAN.md](docs/development/PARITY_PLAN.md), locked after R17. **R17 deferrals all closed**: R17-DEF-1 (2026-05-07) by comprehensive check-fidelity coverage; R17-DEF-2 (2026-05-07) by re-verify against the Agda DBC truth set — B.1 Tier 1 + B.1.x Tier 2 + B.1.x commit-3 senders + Track E VAL_ ship every `DBC` / `DBCSignal` / `DBCMessage` field across all 3 bindings, with FEATURE_MATRIX rows (`dbc_metadata_tier1` / `_tier2` / `dbc_signal_receivers` / `dbc_message_senders` / `dbc_signal_value_descriptions` / `dbc_text_format`) + per-binding parity tests + CHECK 23 `unknown_value_description_target` IssueCode mirror; R17-DEF-3 by Track C.2; R17-DEF-4 by Track B.3; R17-DEF-5 by Track C.3; R17-DEF-6 by Track D.
