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
    ~~~bash
    ACTIONLINT_VERSION=1.7.7
    curl -fsSLO "https://github.com/rhysd/actionlint/releases/download/v${ACTIONLINT_VERSION}/actionlint_${ACTIONLINT_VERSION}_linux_amd64.tar.gz"
    sudo tar xzf "actionlint_${ACTIONLINT_VERSION}_linux_amd64.tar.gz" -C /usr/local/bin actionlint
    ~~~
  - `act` — local GHA replay. Install: `curl -fsSL https://raw.githubusercontent.com/nektos/act/master/install.sh | sudo bash`. Requires Docker.
- **Optional mutation-testing toolchain** (for `tools/run_ci.py --mutation` / `ALETHEIA_MUTATION_CHECK=1` — see [docs/operations/MUTATION.md](docs/operations/MUTATION.md)):
  - **Python**: `mutmut` 3.x via `python/.venv/bin/pip install -e 'python/.[mutation]'` (the `[mutation]` extras pin mutmut exactly, because a mutation baseline is a measured count and its generator cannot float).
  - **Go**: `gremlins` via `go install github.com/go-gremlins/gremlins/cmd/gremlins@latest` (lands in `~/go/bin/`; gremlins substitutes for AGENTS.md cat 14(g) `go-mutesting` because the named tool is unmaintained since 2021 and panics on Go 1.26's `go/types` internals).
  - **C++**: `Mull` 0.34.1 (LLVM-23), built from source by `tools/build_mull.sh` against system LLVM-23 (Bazel; `clang-23` + `llvm-23-dev`; the script carries the patch Mull needs to see LLVM 23) into `~/.local/bin/` as `mull-{runner,reporter,ir-frontend}-23`. Procedure: [docs/operations/MUTATION.md § C++](docs/operations/MUTATION.md); CI caches it (`.github/workflows/pr-heavy-lanes.yml`). The `ALETHEIA_MUTATION` build folds the real-`.so` integration tests into `unit_tests` so FfiBackend is on the mutation surface.
  - **Rust**: `cargo-mutants` at the version `docs/MUTATION_BENCH.yaml` pins (`cargo install cargo-mutants --version <pin> --locked`); the runner refuses any other, and sweeps a scratch copy of the whole tree, never the tree itself (`rust/.cargo/mutants.toml`).
  Each tool's absence is auto-detected by the mutation runner (per-binding skip-with-precise-error); the orchestrator's static gate `tools/check_mutation_setup.py` runs always-on regardless of tool install state.

**Type-check command** (always cap heap):
~~~bash
/home/nicolas/.cabal/bin/agda +RTS -M16G -RTS src/Aletheia/YourModule.agda
~~~
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
- **MEMORY.md**: `wc -m ~/.claude/projects/-home-nicolas-dev-agda-aletheia/memory/MEMORY.md` (the agent store, NOT the repo root), budget **24.4KB as the harness counts it**, which is characters and not bytes: divide `wc -m` by 1024. Leave headroom rather than sitting on the line, since the reported figure is rounded to a tenth. The harness **silently truncates the tail of the file when it is over** (measured 2026-09-20: a 25266-character file loaded with its last two lines cut, while being well inside any line count). If over, compress in-place — move a whole rule family into a hub index file under `memory/` and leave one pointer line naming when to recall it, keeping resident only the rules that must fire when their topic is not signposted; move detail from any over-long or multi-line index entry into its `memory/*.md` topic file and collapse the pointer to a single ≤200-char line; merge or drop stale/duplicate/superseded pointers. MEMORY.md lives in the agent memory store under `~/.claude/` (**outside this repo**), so its reduction is an in-place memory edit, NOT part of the UPD git commit.

**UPD is a doc-state sync only.** The resulting commit must contain ONLY doc-sweep edits. Pre-existing uncommitted work (refactors, structural cleanups, prior tasks) goes in its own commit at task completion, never bundled into UPD. See `memory/feedback_upd_scope.md`. Apply the 2-question pre-commit gate (`feedback_pre_commit_scope_check.md`) before committing the doc sweep.

**UPD frequency rule (token-efficiency).** Run UPD **once per coherent batch close** — not after every single step. In one stretch, 19 UPDs landed across 65 commits (29% of all commits were doc syncs); each UPD re-loads CLAUDE.md (~40 KB), so 19 UPDs amount to ~760 KB of CLAUDE re-reads alone. The right cadence: small-batch work updates `.session-state.md` (gitignored — no token cost to other sessions) during the work, then a single UPD at the end syncs CLAUDE.md / MEMORY.md / PROJECT_STATUS.md. Exception: when a batch surfaces a new durable rule (a new `memory/feedback_*.md` worth indexing) AND subsequent work depends on that rule being indexed, that single rule can warrant its own UPD. When in doubt, defer the UPD to the next natural rest-point.

When the user's message is just `READ` (case-insensitive, no other content), interpret it as **"Read the session state, memory/feedback, plan/project status, CLAUDE.md/AGENTS.md."** Sweep (read-only — no edits):
- `.session-state.md` (gitignored — local resume notes)
- `MEMORY.md` + relevant files under `memory/` (open-work pointers, feedback memories)
- `PROJECT_STATUS.md` (the roadmap/status surface)
- `CLAUDE.md` (already loaded into context)
- `AGENTS.md` (per-language coding standards)

READ is the read-only counterpart of UPD: rehydrate context at session start, do not write.

When the user's message is just `REL` (case-insensitive, no other content), interpret it as **"Cut a release — execute the release runbook."** Walk [docs/development/RELEASE.md § Release runbook](docs/development/RELEASE.md#release-runbook) top to bottom, honoring each step's acceptance gate before moving on. Steps marked ⚑ (the GPG-signed tag, admin tag creation, the GitHub UI flips) are staged into `.commands-to-run.sh` for the user to run; the agent runs the rest. Do not skip the dispatch dry-run before the real tag — the release pipeline runs only on a tag push or `workflow_dispatch`, so it is the only pre-tag exercise of the sign/package/smoke/image path.

### Agda Module Requirements (MANDATORY)

Every Agda module MUST start with:
~~~agda
{-# OPTIONS --safe --without-K #-}
~~~

- `--safe`: no postulates, no unsafe primitives, no non-terminating recursion.
- `--without-K`: HoTT compatibility (no Streicher's K).
- Library-level `--erasure` (in `aletheia.agda-lib`) enables `@0` for zero-cost phantom parameters (e.g. `Timestamp μs`).

**Exceptions**: postulates require a separate `*.Unsafe.agda` module (drop `--safe` only there); allowlisted by name in `shake/Rules/Proofs.hs`. `cabal run shake -- check-invariants` rejects any other `^postulate` line or `Unsafe`-named module, and CI runs `check-invariants` on every build.

### Module Safety Flags

- Default: every module uses `--safe --without-K`.
- The `Main`-family modules add `--no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda).
- Exactly one module drops `--safe`: the allowlisted `--without-K`-only Unsafe substrate `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, which hosts the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the outer-wrap `parseText-on-formatText` consumer — co-located to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

No modules require `--sized-types`. Run `cabal run shake -- count-modules` for the current module inventory.

## Common Commands

See [Building Guide](docs/development/BUILDING.md). Quick reference:

~~~bash
# Type-check a single module
cd src && agda +RTS -M16G -RTS Aletheia/YourModule.agda

# Build everything (Agda → Haskell → libaletheia-ffi.so) — incremental + hash-safe
cabal run shake -- build

# Regenerate the foreign-lib MAlonzo module list (after adding/removing an Agda module)
cabal run shake -- gen-ffi-modules

# IWYU import analysis — regenerates the relevant .agdai (no full .hs/.so rebuild)
cabal run shake -- iwyu

# Tests (each from the right cwd)
cd python && .venv/bin/python -m pytest tests/ -v
cd python && .venv/bin/basedpyright aletheia/ tests/ benchmarks/ ../tools ../benchmarks ../examples ../conftest.py
cd python && .venv/bin/pylint aletheia/ tests/ benchmarks/ ../tools ../benchmarks ../examples ../conftest.py
cd cpp && cmake -B build && cmake --build build && ctest --test-dir build
cd go && go test ./aletheia/ -v -count=1 -race

# Cross-language benchmarks — baseline methodology: 10000 frames × 10 runs,
# identical for all four bindings (the committed benchmarks/results/*_baseline.json
# are generated this way; run all three bench types when refreshing baselines).
# Each mode takes what it reads and refuses what it does not: throughput both
# counts, latency the frame count as its operation count plus the warmup, and
# scaling the run count.
bash benchmarks/run_all.sh --frames 10000 --runs 10 --bench throughput
bash benchmarks/run_all.sh --frames 10000 --warmup 500 --bench latency
bash benchmarks/run_all.sh --runs 10 --bench scaling
~~~

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
- **Shakefile.hs** + **shake/**: build orchestration (Agda → Haskell → shared library); the main registers the rule modules under `shake/`
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

The shim's files hold no business logic:
- **AletheiaFFI.hs**: `foreign export ccall` wrappers around `processJSONLine` (JSON commands) and `processFrameDirect` (binary frames via `aletheia_send_frame`).
- **AletheiaFFI/Marshal.hs**: Agda type construction helpers.
- **AletheiaFFI/BinaryOutput.hs**: binary response encoding.
- **AletheiaFFI/Wire.hsc**: hsc2hs `Storable` reads of the header's structs.
- **cbits/abi_version.c**: the ABI version, readable before the runtime starts.
- **cbits/allocation.c**: the bytes the runtime has allocated, read after a collection; the scaling benchmarks read it around each load.

State managed via `StablePtr (IORef StreamState)`. All bindings load `.so` via ctypes/dlopen — no subprocess overhead.

### C++ Binding (`cpp/`)

Wraps `libaletheia-ffi.so` via `dlopen`. `IBackend` interface; the public double is `make_mock_backend()`, which answers every endpoint with a canned success, and the test-internal `MockBackend` (`cpp/src/detail/`) is the one tests queue responses into. Strong types (`std::byte`, validated newtypes, `std::expected`). Custom `Logger` (~90L, callback-based, 16 event types matching Go's slog, zero-cost when null). RTS cores via `make_ffi_backend(path, rts_cores)` (default 1, once-per-process with mismatch warning). C++23, **Clang 23** (the supported toolchain, see [BUILDING.md § Toolchain support policy](docs/development/BUILDING.md#toolchain-support-policy)); needs a libstdc++/libc++ with C++23 (`<expected>`). Style: `.clang-format` + `.clang-tidy`; the tests and the fuzz harnesses carry their own `.clang-tidy` inheriting the root, disabling only what their frameworks generate.
### Go Binding (`go/`)

Wraps `libaletheia-ffi.so` via cgo + dlopen. `Backend` / `MockBackend` / `FFIBackend` (with C trampolines). Strong types (`[]byte` payload + DLC validation, validated CAN ID / DLC newtypes, sealed CanID/Predicate/Formula interfaces). `slog` via `WithLogger` option (16 event types); `ViolationEnrichment.CoreReason` carries Agda core reason strings. RTS cores via `WithRTSCores` functional option. `Client` is goroutine-safe via a 1-deep channel-token semaphore (`lockCh chan struct{}`) chosen over `sync.Mutex` so that `ctx`-aware `TryLock` cancellation works correctly (see `docs/architecture/CANCELLATION.md`); double-close safe; GHC RTS init thread-pinned (`LockOSThread`). Optional `go/excel/` is a separate Go module pulling `xuri/excelize`; depend on it only for the Excel loader.
### Module Organization

Follow existing package structure (Parser, CAN, DBC, LTL, …). Include correctness properties alongside implementations (`Properties.agda`). Update Main.agda if new functionality needs FFI exposure.

### Import Naming Conventions

When stdlib operators clash, use **subscript suffix** for consistency:
- String: `_++ₛ_`, `_≟ₛ_`
- List: `_++ₗ_`
- Rational: `_+ᵣ_`, `_*ᵣ_`, `_-ᵣ_`, `_≤ᵣ_`

~~~agda
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.Rational using () renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_)

result   = "hello" ++ₛ "world"
combined = list1 ++ₗ list2
~~~

Underscores are invisible in infix usage but remain when passing operators as parameters (e.g., `foldr _++ₛ_ ""`).

## Troubleshooting

Build-time issues are catalogued in [BUILDING.md § Troubleshooting](docs/development/BUILDING.md#troubleshooting). Common ones:

- **Build failures**: `cabal run shake -- clean && cabal run shake -- build`.
- **MAlonzo name mismatch**: build prints exact `sed` command — run it.
- **Type-checking OOM / runaway elaboration**: always cap the heap `+RTS -M16G -RTS`.
- **`hs_init` failure / `aletheia_init() returned null`**: `.so` built against different GHC than loaded. Rebuild (`cabal run shake -- build`); ensure no stale copy in `$LD_LIBRARY_PATH`.
- **`.so` load failure**: every binding reads `ALETHEIA_LIB`; Python's loader then checks `_install_config.LIBRARY_PATH` → `build/libaletheia-ffi.so` → `haskell-shim/dist-newstyle/**`. Regen via `cabal run shake -- install` or set `ALETHEIA_LIB`.
- **`library implements ABI version N`**: `.so` and binding differ in C ABI; rebuild and reinstall both (RUNBOOK.md).
- **DBC validation rejection**: check `ValidationIssue.code` enum — table in [PROTOCOL.md § Error Code Reference](docs/architecture/PROTOCOL.md#error-code-reference). `aletheia validate --dbc <file>` to see all issues.
- **Property formula parse error**: JSON schema is strict (`"operator"` lowercase, predicates under `{"operator": "atomic", "predicate": {...}}`). Compare against `Signal("X").equals(1).to_dict()` output.

## Performance Considerations

- **Parser combinators**: structural recursion on the input list, not fuel — fuel breaks termination or blows up type-checking. See `Parser/Combinators.agda`.
- **Type-checking**: always cap the heap `+RTS -M16G -RTS`; `-N` gives no per-module speedup (see the Type-check command note).
- **Hot path**: `Dec`-valued predicates allocate proof terms per call in MAlonzo. Replace with `Bool`-valued fast path + equivalence lemma. See `extractSignalCoreFast` for the pattern.

## Implementation Phases

[PROJECT_STATUS.md](PROJECT_STATUS.md). Current state: Phase 5.1 complete (binary FFI 4.3× CAN 2.0B / 9.1× CAN-FD; CAN-FD; C++/Go bindings; cross-language benchmarks; four-tier check interface with full parity); the parity plan is complete (matrix gates / DBC text parser / cancellation / doc harness / VAL_ promotion). **Phase 6 (Extensions & New Protocols) is the active track**: shipped so far are the installable distribution (v4.0.0, hardened by v5.0.0), C++/Go CLI parity, the Rust binding and `aletheia template`; open are the Go CAN-log reader and the candidate tracks (native Haskell binding, python-can replacement, GHC native bignum, SOME/IP, which is designed but not scheduled).

---

## Notes for newcomers

Start with the [Project Pitch](docs/PITCH.md) for context.

**Operational pitfalls** (most are caught by build/lint, but easy to trip on first time):
- `Dec`-valued predicates on the streaming hot path: MAlonzo allocates per call. Use `Bool`-valued fast path + equivalence lemma (`extractSignalCoreFast`).
- Fuel-based parser combinators: structural recursion on the input list only.
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

**⚙️ Kernel arcs ✅ MERGED 2026-10-04/06 (#344-#347, #354).** Every frame is parsed in Agda, refused with a typed error or built with its proofs (#344) · a value is written exactly from its proofs or refused, `ValidDBC` carries its erased validity proof, a declared range past a signal's bits is refused at load (#345, BREAKING ×4) · every list in a DBC has a bound, `checkBounds` returns a `BoundedDBC` carrying its erased proof, a refusal names the part that crossed in `field`, `formatDBCText` refuses what every load refuses (#354, BREAKING; `parseDBC` at 20,000 senders 57.54 s to 0.31 s) · a DBC loads in time linear in its length on both routes, `many` stopping when its element parser has not moved (#346); the cross-message checks report one issue per shared key, and the required `load scaling` check holds a load to the doublings of its messages (#347). USER RULE 2026-10-05, *no fuel in the code* ([[feedback_no_fuel]]). Detail: [[project_n33_dbc_load_linear]] + [[project_shipped_arcs_index]].

**🛠️ Lanes and tooling ✅ 2026-09-21..10-08 (#280-#357).** Coverage lane #316 · Rust mutation lane #317 · C entries take structures and the library reports its ABI version #318 (BREAKING ABI) · `aletheia template` in every CLI #321 · kernel text is UTF-8 whatever the locale #328 (BREAKING) · doc-example harnesses run every example #330/#333/#334 · pipeline wall 2424 s to 735 s #336/#337 ([[project_n17_pipeline_time]]) · Go identifiers read at their width #338 (BREAKING Go) · every runnable file parses its arguments #343 · the determinism gate reads a clock or a thread through any name, the build makes the tests' stand-in kernels #353 · a commit leaves its staged files where they were #357. Detail: [[project_shipped_arcs_index]].

**🔬 Probe claims into gates ✅ 2026-10-08..16 (#356, #361, #363, #396, #399, #403, #404, #408-#411).** Each probe runs in a Landlock sandbox of its own (#356) · 60 probes retire, each claim a gate shown red on the probe's defect or a recorded dismissal (#361) · `tools/check_docs.py` runs the arms under `tools/docs_arms/` (#363) · the wide-net probe is the determinism gate's second arm (#396) · the dependency ledger, the comparison script, the benchmark runner and the Go programs hold their claims by gates (#399, #403, #410, #411) · a probe that cannot reach its claim exits 2 (#404) · a fact about a pinned tool is a gate run when the branch moves what it rests on (`tools/pin_scope.py`; #408, #409). USER RULE 2026-10-08, *every property check is a gate, a probe is an investigation's instrument* ([[feedback_property_checks_are_gates]]). Detail: [[project_shipped_arcs_index]].

**🚫 Harnesses and command lines refuse alike ✅ 2026-10-16 (#412, #413).** The four bindings' benchmarks and the three stability harnesses refuse what they dropped, held by child-process tests (#412) · the three CLIs refuse a stray positional, end the flags at `--` and exit 2 naming a failed report write, every refusal a scenario of `docs/CLI_SCENARIOS.yaml` run alike (#413). Detail: [[project_shipped_arcs_index]].

**🔤 Readable replies, the kernel's JSON grammar and the DBC character set ✅ 2026-10-20/21 (#431, #434, #436).** An extracted value whose numerator magnitude or denominator passes 2^63-1 is refused on both extraction paths, a binary frame entry refuses a timestamp past 2^64-1 (`parse_timestamp_past_wire`), and `formatResponse-readable` proves every number a reply writes within the range every binding's reader decodes (#431, BREAKING) · the kernel reads a command as RFC 8259 JSON text and writes every reply as such text, both proven: a raw control character, text after the value or a lone surrogate half is refused, every control character and every key escaped · every DBC string holds printable ASCII but `"` and `\`, plus TAB, LF and CR, a text scanned before it is parsed and the first character outside printable ASCII, TAB, LF and CR refused at its line and column, every name is decided as it is read by the one identifier decision (an ASCII C identifier of at most 128 characters, not a keyword, attribute names included), a `setProperties` signal the DBC does not carry is refused, and each binding reads a `.dbc` file byte for byte; three new wire codes, `dbc_invalid_character`, `dbc_keyword_name` and `handler_unknown_signal` (#434, BREAKING ×2) · the `handler_validation_failed` message is written once, linear in its issues where its join copied the text so far at every step, `python/tests/test_validation_reply_allocation.py` holding a refusal's allocated bytes to ×2.25 per doubling of its issues, red on the old kernel at ×3.53, replies byte-identical (#436). USER RULINGS 2026-10-20, *kernel proves, readers thin* ([[feedback_kernel_is_proof_based]]), *a decision of the user's is asked*; 2026-10-21, *a setProperties signal is one the DBC carries, every name bound by one identifier length, an identifier stops at a character no identifier holds*. USER RULINGS 2026-10-21, evening: the charset kernel's load cost (allocated bytes per load, DBC size +9%, text literal +15%, JSON literal +2%) is *optimised first, then measured against the kept kernels*; after #436, *the `message` stops carrying what `issues` carries, and a refusal row in the four bindings' scaling sweeps replaces the Python-only gate*. Detail: [[project_shipped_arcs_index]].

**🔢 Long numbers, unreadable replies, proof memory, the kernel's error printed alike and load allocation gated ✅ 2026-10-16..20 (#415-#420, #422-#424, #427, #432).** A bound refusal's `observed` stops at 2^64-1, `at least` printed past it, so a 100,001-digit number no longer ends the host process (#419, BREAKING) · a reply the Python reader cannot read raises `ProtocolError` with the decoder's reason (#417) · 200 examples a property test, each running binding code (#416) · the hypothesis, ruff and pylint floors up together (#415), hypothesis pinned (#418), at 6.170.5 with ruff 0.17.1 (#432) · the batch roundtrip proof checks in 1.4 GiB, not 14.2, the warm checker capped at 8 GiB (#420) · every number in a DBC held to 2^63-1 at load, `BoundedDBC` carrying the proof (#422, BREAKING) · the Go binding holds the session handle as an integer (#423, BREAKING Go) · a decimal is decided in the kernel (`aletheia_parse_decimal`), every binding prints the kernel's message verbatim, a loader's refusal is that message with the place it was read, the four loaders held to one answer by `docs/LOADER_SCENARIOS.yaml` (#424, BREAKING ×4) · the kernel reports its allocated bytes (`aletheia_allocated_bytes`, C ABI 3) and the required `load scaling` check holds a load to ×2.25 per doubling of a DBC's messages or of one number's digits (#427, BREAKING ABI). USER RULINGS 2026-10-18, *the kernel is the single source of every error message, printed verbatim, every number decided in the kernel* ([[feedback_kernel_gives_the_error]]); 2026-10-19, *both sweeps on allocation at ×2.25, the JSON path too*; 2026-10-17, *a re-run is no disposition* ([[project_n118_proof_memory]]). Detail: [[project_n115_long_numbers]] + [[project_shipped_arcs_index]].

**🧾 Test processes, toolchain trust and the bundle's licences ✅ 2026-10-13/14 (#389, #391-#395, #397, #398, #400, #401).** A test starts a process only where its claim needs one (2299 starts to 759), marked `@pytest.mark.process` and held by the runtime guard (#389, #391-#395) · the C++ toolchain installs trust their archives with keys in the tree, an unrecorded upstream version refused (#397, #398) · the bundle, `.deb`, `.rpm` and image carry every shipped library's licence text, transitively, held by `check-bundle-licences` and a weekly audit (#401); the SBOM names a GHC 9.8 runtime library at its version (#400). USER RULING 2026-10-14, *the licence obligation is transitive* ([[feedback_licence_obligations_transitive]]). Detail: [[project_n84_bundle_licences]] + [[project_shipped_arcs_index]].

**📏 Source discipline, the commit vocabulary and the release cut ✅ 2026-10-09..13 (#365-#376, #381-#383, #385, #386, #388).** No Go, Rust, C++ or Haskell source file is over 1000 lines (`tools/check_source_length.py`) · a closed commit-subject vocabulary decides which changes owe a CHANGELOG entry, the required `PR title` check holds the squash subject to it · every unwritten C++ local is const · the Python suite is held to determinism while it runs · the documentation gates read Markdown as CommonMark does. USER RULINGS: *no source file over 1000 lines, no exception* (2026-10-09), *squash is the only way in* (2026-10-11), *a refactor carries no CHANGELOG entry*, *a release cut is the base's `[Unreleased]` renamed, in its order* (2026-10-12). Detail: [[project_shipped_arcs_index]].

**🧪 Mutation-lane arcs ✅ MERGED 2026-09-20..10-09 (#274-#278, #358, #360).** C++ survivors to a ledger of zero (#274, [[project_cpp_mutation_surface]]) · the lane as legs and a merge (#275), slices behind ccache (#276), paying only for what the diff can move (#278) · one tree, nine legs to three, 99.6 runner minutes to 39.1 (#358) · every recorded survivor re-examined with the recording kernel as a Shake stand-in (#360). Detail: [[project_shipped_arcs_index]].

**🏷️ Releases.** v5.0.0 2026-07-24, the first tag-triggered release (signed bundle, `.deb`/`.rpm`, GHCR image; the dry-run and the tag each caught a release-path defect) → [[project_v5_release]] + CHANGELOG [5.0.0]. v4.0.0 2026-07-17, the first self-contained multi-binding bundle → [[project_r26_product_gaps]]. v3.0.0 #171 · v2.0.0 #18.

**USER RULE 2026-07-19**: prose about code carries no hard-coded counts and no line-number references — describe structure qualitatively or name the SSOT; measurements, spec constants, versions/dates, and machine-re-derived numbers keep their digits (`memory/feedback_self_referential_count_drift.md` + AGENTS/docs.md cat 14).

**Earlier arcs ✅ CLOSED** (indexed in [[project_shipped_arcs_index]]): distribution hardening #213-#216 · wire-code SSOT #211 · E.2 route (b) #181-#187 [[project_e2_reexamination]] · memory-citation gate #195/#196 · gate soundness #190-#194 [[feedback_gate_pass_is_absence_of_output]] · merge queue and binding review #80-#168 [[project_r25_binding_review]] · CI speed, incremental build and caching #7/#37/#51/#122 [[project_ci_speed_optimization]] · mutation to zero #16/#71/#72 [[project_mutation_to_zero]] · Rust binding #53-#77 [[project_rust_parity_r1]] · CLI parity #21 · release signing #20 [[project_release_signing_hardening]] (GPG key expires **2028-06-10**, renew before) · A.2 `BO_TX_BU_` senders [[project_a2_botxbu_senders]] · FEATURE_MATRIX semantics #23 [[feedback_feature_matrix_status_semantics]].

**Standing way of working** (still current): user GPG-signs all commits via the `.commands-to-run.sh` dribble; attribution = the active Claude model's `Co-Authored-By` + the Claude Code PR footer (`memory/feedback_commit_workflow_signed.md`); pipeline-PRs; ultracode.

**Branch & PR hygiene ✅ ENFORCED**: `.github/workflows/pr-full-ci.yml` runs `tools/run_ci.py` (all gates) on every `pull_request` + `push:main`; the `main` ruleset **requires** `tools/run_ci.py (all gates)` (2026-06-10), **`mutation testing`** (#72), **`load scaling`** (allocated bytes per load held to the doublings of a DBC's messages or of one number's digits) **and `PR title`** (#376, the squash subject in the closed vocabulary); squash is the only merge method. Detail: `docs/development/BRANCH_PR_HYGIENE.md`, `memory/project_cpp_compilers.md`.

**Pending work** lives in ONE place: `memory/TASKS.md`, the single local task list (agent store, outside this repo). Nothing in the tree records a task, and nothing in the tree may cite that file — `tools/check_no_memory_citations.py` refuses a memory citation in source or docs, so an in-source note states its constraint in its own words. A task is not only implementation: research and analysis, design, testing, validation and release work are tasks too, and the list carries a design task with its plan in full. What is open is read from the list; this file names no task.

**Standard gates** (all run by `tools/run_ci.py`; the full ordered sequence is [AGENTS.md § Step 4](AGENTS.md#step-4-implement-and-verify), the canonical source): Agda `build` + the proof gates (`check-properties` and siblings), Python `pytest`, Go `go test -race`, C++ `ctest` (Clang 23), tree-wide lint (ruff / pylint / basedpyright), IWYU (`tools/iwyu.py`), GHA meta (actionlint / pin / permission checks), and SPDX headers.

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

**Cross-binding parity**: tracked in [docs/FEATURE_MATRIX.yaml](docs/FEATURE_MATRIX.yaml) (the parity plan is complete). Every `DBC` / `DBCSignal` / `DBCMessage` field (Tier 1 and Tier 2 metadata, signal receivers, message senders, VAL_ value descriptions) ships in every binding, with FEATURE_MATRIX rows, per-binding parity tests and the CHECK 23 `unknown_value_description_target` IssueCode mirror; check-fidelity coverage, the cancellation contract, the DBC text round-trip and the doc-example harness are complete (2026-05-07).
