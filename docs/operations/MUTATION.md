# Mutation Testing — operations guide

Mutation testing runs across all four bindings.
The actual tools are: **Python** via `mutmut`, **Go** via `gremlins`
(substituted for the AGENTS.md cat 14(g)–named `go-mutesting`, which is
unmaintained — see § Per-binding sub-checks), **C++** via `Mull`, **Rust**
via `cargo-mutants`.  This doc
explains the threshold model, the per-binding sub-checks, the env-var
contract, the install procedure, and the forward-revert verification
protocol.

A finding survives a mutation when the test suite still passes after the
mutation operator transforms operational code (e.g. flips `<` to `<=`).
AGENTS.md cat 14(g): **"an unjustified survivor is a test gap"**.  The
mutation lane is a per-PR signal, not per-commit (cost is high — 30 min to
2 hours per binding).

## Architecture

```
docs/MUTATION_BENCH.yaml           SSOT — per-binding tool, hot-path module list, baseline
tools/check_mutation_setup.py      Static gate (offline, ~1 sec)
tools/mutation_run.py              Dynamic runner (opt-in, ~30 min - 2 hours)
tools/mutation_cpp.py              The C++ lane: Mull over the trees, in stages
tools/mutation_cpp_legs.py         The C++ lane's trees, legs and stage variables
tools/mutation_cpp_slices.py       The C++ surface's partition into slices
tools/mutation_rust.py             The Rust lane: cargo-mutants over the crate, in place
tools/mutation_report.py           The report and baseline shapes the lanes share
tools/mutation_routes.py           The C++ kill-route census
benchmarks/mutation/<short-sha>/   Per-commit JSON + raw tool logs (gitignored)
```

The static gate (`tools/check_mutation_setup.py`) runs always-on
(`check-mutation-setup`) in `tools/run_ci.py`; it fires when a hot-path
source file is renamed or deleted without updating the YAML.  The dynamic runner is opt-in via
`ALETHEIA_MUTATION_CHECK=1` or `tools/run_ci.py --mutation`.

In CI the runner is invoked once per binding, in parallel lanes with their own
budgets, each told to skip the others (`ALETHEIA_MUTATION_SKIP_PYTHON` /
`_GO` / `_CPP` / `_RUST`), because the four tools cost wildly different amounts
and one job charges the slowest against a clock the others have already spent.  The
C++ lane is nine legs and a merge: a leg sweeps one slice of one mutation tree
(`ALETHEIA_MUTATION_CPP_STAGE=leak`, `plain` or `address`,
`ALETHEIA_MUTATION_CPP_SLICE` the slice), reports as the binding `cpp-leak-1`
and so on, and judges no survivor, since it has read neither the rest of its
tree nor the other trees, where the mutant it let live may die; the
`mutation cpp` job downloads every leg's reports, unions each tree's slices
and intersects the trees over the mutants each carries
(`ALETHEIA_MUTATION_CPP_STAGE=merge`, the directory in
`ALETHEIA_MUTATION_CPP_LEGS`), which is where the C++ survivors meet the
baseline and the ledger. How the slices are cut, and what the merge refuses,
is below.  The merge refuses a leg whose reports are missing or
doubled, or whose summary records another commit.  The
`mutation testing` check the branch ruleset requires reports those lanes and
the merge: it passes only on the single result meaning every one of them
finished clean, and refuses every other, a job killed by its own budget
included.  Each run records its lanes' wall times under `elapsed_s` in
`summary.json`, and the merge records each leg's in `cpp-legs.json` beside it,
so a budget is set from a measurement: the lane's slowest recorded wall clock
plus what its cache misses cost, the arithmetic beside each budget in the
workflow.  Every lane uploads its report directory as an artifact whatever
ended it.

The long-running commands stream their output rather than having it captured:
a lane killed by its budget would otherwise take its entire log with it, and
while it runs there would be no way to tell progress from a hang.

## Threshold model

Two-tier per advisor 2026-05-09:

- **Drift gate (hard equality)** — observed survivor count must not exceed
  the baseline recorded in `docs/MUTATION_BENCH.yaml`.  Any new survivor is
  a finding, surfaced via the runner's exit code = 1 with a JSON report
  pointing at the file/line.
- **Timeout ceiling**: a mutant the tool could not finish testing is
  neither killed nor survived, so a sweep that timed out on nearly all of
  them reports no survivors at full efficacy.  Where a binding's baseline
  records `timeout_ceiling`, a run past it fails the lane whatever its
  survivor count.  The Go lane records one; the other two tools report no
  such bucket.
- **Kill routes (C++, recorded, not gated)**: Mull's SQLite report keeps each
  mutant's exit status and the test binary's output, and the runner reads
  from them what ended every run: a test's assertion, a leak the sanitizer
  reported, the kernel ending the process, a check the standard library runs
  in the mutation build (the trees compile under libstdc++'s debug mode, so a
  read past a container's end or an out-of-range subscript ends the run at that
  step, with its message), or a fault (a signal).  A mutant several lanes
  killed is attributed in that order.  The counts land in `cpp-routes.json`
  beside `cpp.json` and in the C++ baseline; a probe holds them equal to the
  record, which the pinned test order and the debug-mode checks make exact, and
  a sweep with any timeout is reported as a census taken under load rather than
  compared.  The mutants attributed to a check or a fault are the ones no test
  observes by behaviour: what each changes, a guard for most of them and the
  value an index is computed from for the rest, leads straight to an operation
  the language does not define.
- **The not-covered ledger (Go, gated)**: gremlins puts a mutant on a line no
  test executes in a bucket of its own, neither killed nor lived, and the Go
  baseline records the count as `not_covered` and each such mutant as a row of
  `not_covered_ledger`, by mutator, repository-relative file, source-line text
  and the count sharing the line. The lane fails on more of them than the
  record and on a row the ledger does not name, at any count, since either is
  a line that lost its test; a row the sweep no longer produces is reported as
  stale and lowers the record. What the ledger names is package-level
  constants, whose declarations Go's cover profile does not mark as statements,
  so no test executes them and gremlins never tries their mutants; the values
  are held by the tests that read them. The coverage lane
  ([COVERAGE.md](COVERAGE.md)) is the same gap seen from the suite's side.
- **The unobserved ledger (C++, gated)**: those kills are recorded in the C++
  baseline as `unobserved_ledger`, a row per mutator, repository-relative file,
  source-line text, route and refused invariant, with the count of mutants
  sharing the line.  The lane refuses a kill the ledger does not name, as it
  refuses an unrecorded survivor, and reports a row the sweep no longer
  produces without failing on it, so a test that learned to observe one does
  not fail the change that wrote it; the probe over the ledger refuses that
  direction too, and the change lowers the record.  The row is keyed on the
  line's text and not its number, and the refusal is recorded down to its
  invariant without the index and size the check printed, because those come
  from the test data.  `tools/check_mutation_setup.py` holds every row of both
  ledgers to a file and a line the tree still has, in the always-on sweep, so a
  rename or a reworded line surfaces in seconds rather than at the end of a
  mutation run.  The lane writes the same rows to `cpp-unobserved.json` beside the
  census and prints them in its log, so re-taking the ledger is a copy.
- **First run (no gate)** — when the YAML baseline is `null`, the runner
  records the observed survivor count as informational and exits 0.  The
  next commit is expected to either match this count or improve on it; the
  `null → integer` transition happens via an explicit baseline-set commit
  (NOT by silent overwrite).

The gate is per-binding: a regression in one binding fails the lane even
if the others stay clean.  Each binding's tool reports survivor counts
independently.

## Per-binding sub-checks

| Binding | Tool | Hot path (per AGENTS.md cat 14(g) + actual paths) |
|---|---|---|
| Python | `mutmut` 3.x | `aletheia/client/_client.py`, `aletheia/dbc/_converter.py`, `aletheia/yaml_loader.py`, `aletheia/codes/_issue.py`, `aletheia/types.py` |
| Go | `gremlins` | `aletheia/client.go`, `dbc.go`, `json.go`¹, `ffi.go`, `ffi_nocgo.go`, `enrich.go`²; the stringer outputs are held out by `go/.gremlins.yaml` |
| Rust | `cargo-mutants`, pinned in `docs/MUTATION_BENCH.yaml` | `src/response.rs`, `src/dbc.rs`, `src/types.rs`, `src/backend.rs`, named by `rust/.cargo/mutants.toml`, which the tool reads from the crate; swept in place, because the suite includes the DBC corpus and the parity snapshots from above the crate at compile time |
| C++ | `Mull` 0.34.1 (LLVM 23, from source) | `cpp/src/*.cpp` less `mock_backend.cpp` / `types.cpp` (test-only / type-defs) and `rational_renderer.cpp`, with the exact mutated set enumerated in `docs/MUTATION_BENCH.yaml`; the mutator set (`cxx_default`, the decrement, assignment, bitwise and negation groups, and the four call mutators), what each class of mutant stands for, and the held-out paths (vendored, system, `cpp/tests` and the test double under `cpp/src/detail`) are `cpp/mull.yml`; the build records each unit's command line so that Mull's junk detector can re-parse it, without which it drops every mutant of a unit it cannot parse |

AGENTS.md cat 14(g) names `gomut` / `go-mutesting` / `mutate` for Go.  We use
**`gremlins`** (`github.com/go-gremlins/gremlins`) instead because both
zimmski/go-mutesting (last commit 2021) and avito-tech/go-mutesting fail
on current Go: zimmski panics in `go/types` internals, avito doesn't
resolve multi-file packages cleanly.  Gremlins covers the same operator
set (CONDITIONALS_NEGATION / ARITHMETIC_BASE / INVERT_NEGATIVES /
CONDITIONALS_BOUNDARY) with the same intent, and is actively maintained.

¹ AGENTS.md `protocol.go` → actual `json.go` (request/response protocol marshaling).
² AGENTS.md `frame.go` → actual `enrich.go` (per-frame violation enrichment).

The actual-vs-AGENTS.md mappings are recorded in `docs/MUTATION_BENCH.yaml`
to keep prose drift catchable: AGENTS.md is the canonical *requirement*,
the YAML is the actual *configuration*.

## Installation

The mutation lane is opt-in only, so the tooling is NOT in the project's
default `[dev]` extras.  Install once:

### Python — `mutmut`

```bash
cd python
.venv/bin/pip install -e '.[mutation]'
.venv/bin/mutmut --version    # expect the version pyproject.toml pins
```

The `[mutation]` extras section in `pyproject.toml` pins mutmut to one exact
version, and that pin is the only place the version is written.  A range is
wrong here for a reason a range is right elsewhere: two mutmut releases in the
same major enumerate different mutant sets, so a contributor resolving to the
floor and CI resolving to the ceiling measure different populations, and the
survivor CI reports cannot be reproduced locally at all.  A baseline that is a
measured count cannot float its generator.  Bumping the pin is deliberate and
re-measures the Python row of `docs/MUTATION_BENCH.yaml`.

mutmut's operator table is fixed in the package and takes no configuration,
so what it cannot mutate is a refusal the lane carries whole: a `return`, a
`raise`, a condition that is a bare name or call, an f-string, a `for` or a
`with`, and any function under a decorator other than `staticmethod` or
`classmethod`, which it skips entire. A defect in one of those is one the
Python lane cannot see, and the probe
`probes/python_pyproject.toml--mutmut-has-no-operator-for-these-constructs.sh`
holds the pinned version to that list, so a release that gains an operator
re-opens the row rather than counting silently.

### Go — `gremlins`

```bash
go install github.com/go-gremlins/gremlins/cmd/gremlins@latest
which gremlins    # expect: ~/go/bin/gremlins
```

`~/go/bin` should already be in `$PATH` — verify with `echo $PATH`.

(Per the table above, `gremlins` substitutes for the AGENTS.md-named
`go-mutesting`; both reach the same operator set.)

### Rust — `cargo-mutants`

```bash
cargo install cargo-mutants --version 27.1.0 --locked
cargo mutants --version    # expect the version docs/MUTATION_BENCH.yaml records
```

The record pins the version exactly and the runner refuses any other, for the
reason mutmut is pinned: two releases generate different mutant sets, and a
baseline is a count of one set.  Bumping the pin re-measures the Rust row.

The sweep runs in the source tree (`--in-place`) rather than in the copy
cargo-mutants makes by default, because the crate's suite includes the DBC
corpus and the parity snapshots under `python/` at compile time and reads the
documents under `docs/` at run time, so a copy of the crate alone does not
build.  In place, one mutant runs at a time; cargo-mutants restores the file
after each mutant and on an interrupt, and a process killed outright leaves
the mutant in the tree, where `git diff rust/src` shows it.  Nothing else may
build or test the crate while a sweep runs.  What is mutated and with which
features is `rust/.cargo/mutants.toml`, read from the crate, so a sweep at the
terminal and the lane's sweep make one set.

### C++ — `Mull`

The project supports only the latest stable Clang (23), and UB can differ
between compiler versions, so the mutation lane MUST test clang-23 codegen.
No prebuilt Mull deb ships past LLVM 15, and Mull 0.34.1 itself stops at LLVM
22, so `tools/build_mull.sh` **builds Mull from source** against the system
LLVM-23 with the patch that lets it see LLVM 23: its supported-version list,
the one call in libirm that LLVM 23 removed, and libirm taken at the commit
that truncates a call replacement's constant to the call's width, without which
`cxx_replace_scalar_call` aborts clang on the first `bool`-returning call it
meets. The same build gives every mutant an identifier of its own
(`tools/mull/mull-unique-mutant-ids.patch`): Mull names a mutant by mutator and
source range, so two mutations of one statement (a temporary's destructor on
the normal path and in the exception-cleanup landing pad) or two instantiations
of one template shared a name, and the trampoline ran only the last clone it
registered while the report counted the others under it. The identifier gains a
seventh part, a hash of the function's mangled name and an ordinal among that
function's mutants of the same range, so every clone runs and is reported on
its own; the probe
`probes/tools_build_mull.sh--every-mutant-identifier-names-one-clone.sh`
holds the installed plugin to that patch. The same build teaches the two
call mutators the `invoke` instruction
(`tools/mull/libirm-void-call-mutator.patch`,
`tools/mull/libirm-scalar-call-invoke.patch`): at `-O0` with exceptions on, a
call that can throw is an `invoke`, a different opcode, so as shipped neither
mutator ever reached a call the source writes that can throw, and the void-call
mutator reached only the implicit destructors of temporaries, which are
`noexcept`. The same build lets both call mutators reach a call through a
function pointer, which libirm refused as indirect
(`tools/mull/libirm-call-replacement-indirect.patch`,
`tools/mull/libirm-void-call-indirect.patch`): the backend calls every kernel
entry through one, so before it no mutant dropped a kernel call or made the
kernel answer something else. And it adds two replacements the scalar one
could not make (`tools/mull/mull-call-replacement-kinds.patch`): the scalar
constant truncates to false on a call returning `bool`, so
`cxx_replace_bool_call_true` is the other answer, and
`cxx_replace_pointer_call_null` answers a pointer-returning call with null,
made only where null is an answer the caller reads, a call through a function
pointer or a result compared with null, since a string's data or an
exception's message never answers null and replacing it would measure the
language's undefined behaviour. Those destructors are a mutator of their own,
`cxx_remove_implicit_destructor` (`tools/mull/mull-implicit-destructor-mutator.patch`),
which `cpp/mull.yml` leaves out of the swept set: it removes a call the
compiler emits and the source never writes, and on this tree every one it
reaches is the destructor of a temporary a value-returning function handed to
a container, moved from before it runs, so no defect in the project can change
what the removal does. It stays in the plugin so that such a removal is never
reported as the removal of a call the source wrote. The lane's tree is built under
LeakSanitizer (`-DALETHEIA_SANITIZER=leak`), so a removed call whose object
owned memory leaks and fails, which is what holds a released handle or string
to its release. The binaries land in
`~/.local/bin/` (no sudo for the copy), which the project assumes is on
`$PATH` (see CLAUDE.md § Development Environment).

Two instruments beside the sanitizer make a mutant observable that no
assertion on a result could see. The allocation-fault harness also counts a
call's allocations, so a container reserved ahead is told from one left to
grow, and the ack fast path from the parse it skips; its sweeps find a call's
own allocations by one recorded run, naming the frames above each, so the
allocations of a vendored library, which may not be failed, are never failed,
and the loaders are swept whole. And a kernel stand-in
(`cpp/tests/kernel_stand_in/`) carries every symbol the backend and the
renderer resolve and refuses every call with a message quoting its arguments,
which is the one way to read what the backend marshals to an entry whose
arguments the real kernel acknowledges without reading: the timestamp of an
error or remote event, and the CAN-FD bus bits of a frame.

A destructor a container's growth would run while it throws is reached by
failing an allocation, which `cpp/tests/alloc_fault.cpp` does: it replaces the
program's allocation functions, counts the blocks the program holds, and fails
one chosen allocation of a call, so a cleanup path that drops what it owns
shows as a count that did not come back. The sweeps over the decoders and the
builders are in `cpp/tests/unit_tests_alloc_fault.cpp`. They build in the
lanes that run without a sanitizer, because a sanitizer runtime carries the
same allocation functions and the two cannot be linked together, and they
leave the JSON library's own allocations alone, since that library flattens a
document onto a heap-allocated stack from a destructor and an exception
leaving a destructor ends the program. The probe
`probes/cpp_tests_alloc_fault.cpp--the-json-document-cleanup-cannot-take-a-failed-allocation.sh`
holds both halves of that.

```bash
# System LLVM-23 + clang-23 (one-time; apt.llvm.org on Ubuntu, the archive on Debian).
sudo apt install clang-23 llvm-23-dev libclang-23-dev

# Build Mull 0.34.1 from source into ~/.local/bin.  bazelisk is fetched there
# and reads Mull's .bazelversion; the build uses the system LLVM via
# /usr/lib/llvm-23, so no LLVM is downloaded.
tools/build_mull.sh

# Verify: a from-source build prints the unstamped banner.
mull-runner-23 --version    # mull-runner {STABLE_MULL_VERSION}
```

`mull-runner` / `mull-reporter` are Rust binaries; `mull-ir-frontend-23` is a
C++ clang plugin `.so`.  The standard build (`cmake -B build`) also requires
`clang++-23` (the project supports the latest stable Clang only; g++
unsupported); the mutation lane uses the same `clang++-23` inside its three
dedicated trees, `cpp/build-mutation/`, `cpp/build-mutation-plain/` and
`cpp/build-mutation-asan/`.  CI caches the clang-23 debs, the from-source Mull
build (keyed on the Mull tag + LLVM version) and, per lane, the compiler cache
of its tree's objects under a cap the lane's own comment sizes from a
measurement; see `.github/workflows/pr-heavy-lanes.yml`.  The repository's
Actions cache as a whole is kept under its ceiling by
`.github/workflows/cache-prune.yml`, which runs `tools/prune_actions_cache.py`
on every closed pull request and once a day: a closed request's entries, which
nothing can restore, and the entries on `main` a newer one under the same key
prefix has superseded are deleted, and nothing else is.

On a pull request the runner sweeps only the bindings whose directory the diff
against `main` touches, and each CI lane installs only the toolchain its own
sweep needs: the lane asks `tools/mutation_scope.py`, which reads that same
scope, ahead of its install steps rather than after them. A change under the
Agda kernel, the FFI shim, any module of this harness or the recorded
baselines is every binding's change, and a push to `main`, whose diff is
empty, sweeps every binding.
Set `ALETHEIA_MUTATION_NO_DIFF_SCOPE=1` to sweep everything regardless.

## Running the lane

### Via the orchestrator (recommended)

```bash
tools/run_ci.py --mutation                 # always-on steps + mutation lane
tools/run_ci.py --full                     # everything (san + repro + stability + mutation)
ALETHEIA_MUTATION_CHECK=1 tools/run_ci.py  # legacy env-var trigger (still supported)
```

Exit code 0 = lane clean; exit code 1 = drift gate failed (see
`benchmarks/mutation/<short-sha>/summary.json` for the diagnostic).

### Per-binding directly

```bash
# Python
cd python && ALETHEIA_LIB=$PWD/../build/libaletheia-ffi.so .venv/bin/mutmut run
.venv/bin/mutmut results

# Go
cd go && gremlins unleash ./aletheia

# Rust (needs build/libaletheia-ffi.so, which the suite loads through
# ALETHEIA_LIB).  In place: nothing else may build or test the crate meanwhile.
cd rust && ALETHEIA_LIB=$PWD/../build/libaletheia-ffi.so cargo mutants --in-place

# C++ (needs build/libaletheia-ffi.so — the ALETHEIA_MUTATION build folds the
# real-.so integration tests into unit_tests to cover FfiBackend, so run
# `cabal run shake -- build` first).
# A mutant survives only where every tree carrying it let it: the leak tree
# reads a destructor removal that leaks, the address tree a value read after
# what held it has gone, and the plain tree carries the allocation-fault
# sweeps, which no sanitizer tree can carry because a sanitizer defines the
# allocation functions they replace.  The address tree drops the mutators
# over calls and over constant stores, whose mutants there are the
# sanitizer's own inserted checks and stores.
cd cpp
cmake -B build-mutation -DALETHEIA_MUTATION=ON -DALETHEIA_SANITIZER=leak \
      -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23
cmake --build build-mutation --target unit_tests
# The lane's own flags: the cap per mutant, since Mull's default of ten times
# the baseline ends the slow mutants under debug mode, and the pinned order.
# The cap on the runner's runs of the unmutated binary is cpp/mull.yml's.
mull-runner-23 --minimum-timeout=600000 ./build-mutation/unit_tests -- --order decl
cmake -B build-mutation-plain -DALETHEIA_MUTATION=ON \
      -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23
cmake --build build-mutation-plain --target unit_tests
mull-runner-23 --minimum-timeout=600000 ./build-mutation-plain/unit_tests -- --order decl
# The address tree builds under a configuration the lane generates beside it,
# which is `cpp/mull.yml` without the call and constant-store mutators; the runner is given
# the same file, so the tree and the sweep read one mutator set.
python/.venv/bin/python -c 'from pathlib import Path
from tools.mutation_cpp import leg_config
from tools.mutation_cpp_legs import CppLeg, CppTree
print(leg_config(CppLeg(CppTree.ADDRESS), Path("cpp/build-mutation-asan")))'
cmake -B build-mutation-asan -DALETHEIA_MUTATION=ON -DALETHEIA_SANITIZER=address \
      -DALETHEIA_MULL_CONFIG="$PWD/build-mutation-asan/mull-config.yml" \
      -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23
cmake --build build-mutation-asan --target unit_tests
MULL_CONFIG="$PWD/build-mutation-asan/mull-config.yml" \
  mull-runner-23 --minimum-timeout=600000 ./build-mutation-asan/unit_tests -- --order decl
```

Per-binding skip env vars (useful for partial runs):

```bash
ALETHEIA_MUTATION_SKIP_PYTHON=1   # skip Python lane only
ALETHEIA_MUTATION_SKIP_GO=1       # skip Go lane only
ALETHEIA_MUTATION_SKIP_CPP=1      # skip C++ lane only
ALETHEIA_MUTATION_SKIP_RUST=1     # skip Rust lane only
```

The C++ lane in stages, as CI runs it (unset, the runner sweeps every tree in
one process and merges them itself):

```bash
ALETHEIA_MUTATION_CPP_STAGE=leak    # sweep the leak tree alone; reports as cpp-leak, judges nothing
ALETHEIA_MUTATION_CPP_STAGE=plain   # the plain tree likewise, as cpp-plain
ALETHEIA_MUTATION_CPP_STAGE=address # the address tree likewise, as cpp-address
ALETHEIA_MUTATION_CPP_STAGE=merge \
ALETHEIA_MUTATION_CPP_LEGS=<dir>    # sweep nothing; merge the legs' reports found under <dir>
```

## Setting / updating a baseline

After a clean run on `main`:

```bash
ALETHEIA_MUTATION_CHECK=1 tools/run_ci.py
cat benchmarks/mutation/<short-sha>/summary.json
# Edit docs/MUTATION_BENCH.yaml: replace `survivors: null` with the observed count
# Commit the YAML edit with rationale ("baseline established at <sha>; <N> survivors")
```

A baseline regression (observed > baseline) MUST be addressed by:

1. Investigating the new survivor in `benchmarks/mutation/<short-sha>/<binding>.raw.txt`
2. Either: writing a test that kills the mutant (preferred), OR adding a
   `# pragma: mutmut-no-mutate` comment block at the source site naming
   why the mutant is equivalent / unreachable / non-operational (per
   AGENTS.md "an unjustified survivor is a test gap"). For C++, a survivor
   that is kept is also recorded in the baseline's `survivors_ledger` in
   `docs/MUTATION_BENCH.yaml`, by mutator, repository-relative file, the text
   of its source line and how many share that line; the lane refuses a
   survivor the ledger does not name even at an unchanged count, and reports
   a row that no longer survives as stale. The Rust lane keys its rows the
   same way, the mutator being the mutation cargo-mutants names less its
   position, read from `mutants.out/outcomes.json` under the lane's `rust/`
   artifact directory. The lane's `cpp-mull.json` artifact
   is Mull's Elements report of each tree, merged by
   `tools.mutation_cpp.merge_elements` over the union of the trees' mutants,
   so a mutant any tree carrying it killed is killed, and `tools.mutation_cpp.elements_survivor_rows`
   renders what is left in the ledger's row shape. The probe
   `probes/docs_MUTATION_BENCH.yaml--every-cpp-survivor-is-a-recorded-one.sh`
   holds the ledger exact in both directions. Beside each lane's Elements
   report the lane keeps Mull's SQLite report of it, which is where the kill
   routes are read from. To run one C++ mutant alone
   against a test, set its identifier from the Elements report as an
   environment variable of the mutation binary:
   `env "<id>=1" cpp/build-mutation/unit_tests '<filter>'`.
3. Re-running the lane to confirm no regression.

A baseline IMPROVEMENT (observed < baseline) is permitted to land via the
same YAML edit pattern; the new lower count becomes the floor.

## Forward-revert verification protocol

Every gate's shape is verified by injecting a violation and confirming the gate
fires with a precise diagnostic.

### Static gate (`tools/check_mutation_setup.py`)

```bash
# Inject violation: rename a hot-path entry in YAML to a non-existent path.
sed -i 's|aletheia/client/_client.py|aletheia/client/_NONEXISTENT.py|' \
    docs/MUTATION_BENCH.yaml
python/.venv/bin/python -m tools.check_mutation_setup
# Expect: exit 1 with diagnostic naming the missing path.

# Restore.
git checkout docs/MUTATION_BENCH.yaml
python/.venv/bin/python -m tools.check_mutation_setup
# Expect: exit 0, naming every hot-path source present.
```

### Drift gate (per binding)

```bash
# Set baseline to 0 in YAML for one binding.
# Inject a survivor by replacing an assertion with a tautology
# (e.g. `assert x == 1` -> `assert x == x`).
# Run the mutation lane.
ALETHEIA_MUTATION_CHECK=1 tools/run_ci.py
# Expect: exit 1 with summary.json showing observed_survivors > baseline.

# Restore source + YAML; re-run.
git checkout python/aletheia/client/_client.py docs/MUTATION_BENCH.yaml
ALETHEIA_MUTATION_CHECK=1 tools/run_ci.py
# Expect: exit 0.
```

## CI wiring

| Step | Frequency | Cost | Trigger |
|---|---|---|---|
| Static gate (`check-mutation-setup`) | Every push (via pre-push hook) | <1 sec | Always-on (`check-mutation-setup`) in `run_ci.py` |
| Dynamic gate (`mutation testing`) | Per PR | ~30 min - 2 hrs | Opt-in via `--mutation` / `ALETHEIA_MUTATION_CHECK=1` |

The static gate guards against silent rename / removal of a hot-path file
without YAML update — a config-vs-reality drift class, but for hot-path file paths.  The
dynamic gate is the actual mutation pass; per AGENTS.md "once per PR is
sufficient; per-commit is overkill".

## The C++ lane's slices, and the weights they are cut on

The C++ sweep is the slowest of the three, and one CI job per mutation tree
still charged the clock of a whole tree's sweep against a single runner.  Each
tree is therefore swept by three jobs, each building the tree under a Mull
configuration that holds the other slices' files out, so a job carries its own
slice's mutants alone.  The `mutation cpp` job unions each tree's slices, then
intersects the trees, and that union is the verdict the drift gate reads.

**Nothing keeps a list of which file is in which slice.**  The set a slice can
claim is derived: every tracked file under `cpp/src`, `cpp/include` and
`cpp/benchmarks` that `cpp/mull.yml` does not already hold out, the last for
the header the benchmark harness keeps its timed loops in, which the unit tests
instantiate.  A file added to the library is in that set the moment it is
tracked, and `tools/mutation_cpp_slices.py` computes the partition from it.
The slices state what they *hold out* rather than what they claim, which
decides how a mistake surfaces: a file no slice claims is
mutated by all three, so its mutants arrive once per slice and the merge
refuses the repeated identifiers.  Stating what a slice claims would instead
drop that file and report the smaller census as a clean sweep.

Two refusals guard the union.  A mutant carried by two slices of one tree is
refused by identity, as above.  A union *below* the recorded `total_mutants` is
refused as a slice that carried fewer files than the partition gave it; a
census that grew is ordinary work and passes, and a deliberate removal lowers
the record in the same commit, the way the survivors baseline is lowered.

**The weights are balance, never coverage, and they are reviewed on a
schedule.**  The partition is balanced by `mutants_by_file` in
`docs/MUTATION_BENCH.yaml`, the mutants each file carried when the census was
last taken, which stands for the sweep's cost because the cost of a mutant
hardly varies.  A file the record does not name still lands in a slice; it
simply weighs nothing, which is right for the files that carry no mutants and
costs a newly added file some balance until the census is re-taken.  Because
adding code adds mutants and nothing refuses that, these counts age quietly in
one direction.  So the merge prints, beside its verdict, what the heaviest
slice would carry today under the recorded weights against an equal share,
counted in mutants: fresh weights read about nothing there, measured at 0.0
percent on the run that recorded them, and the figure grows as the surface
outgrows the record.  The review that re-takes them is scheduled against it
rather than against a date (AGENTS.md § Universal Rules; the task list carries
it).  How evenly the cut divides the sweep's *time* is a separate measurement,
taken from the recorded per-mutant durations rather than printed by any run,
and is what says whether three slices is still the right number.  Re-take
by reading `cpp-files.json` from the merge's artifacts into `mutants_by_file`.

Changing the partition changes every slice's configuration, which the compiler
cache keys on, so the run after such a change rebuilds all six trees.  It is
also why a slice's build tree records the digest of the configuration it was
built under and is discarded when that differs: nothing in CMake knows an
object depends on the Mull configuration, so a tree left from another slice
would answer a rebuild by doing nothing and sweep the other slice's mutants.

## Scope notes

**Cluster 7 ships infrastructure, not survivor elimination.**  The
threshold model treats baseline as a starting point: the first run sets
it via an explicit YAML edit; subsequent runs guard against regression.
Eliminating the initial baseline survivors is a separate follow-up
backlog item — they are individual findings (per AGENTS.md "an unjustified
survivor is a test gap"), each tracked / addressed in their own PRs.

The infrastructure was designed so that the survivor-elimination work is
incremental: kill one mutant by adding a test → re-run lane → update YAML
baseline `survivors` count downward → commit.  No tooling re-bootstrap
needed.

## See also

- `AGENTS.md` cat 14(g) (Python / Go / C++ / Rust) — canonical hot-path lists
- `docs/MUTATION_BENCH.yaml` — actual on-disk paths, baseline numbers
- `tools/check_mutation_setup.py` — static gate (always-on)
- `tools/mutation_run.py` — dynamic runner (opt-in)
- `tools/mutation_cpp.py`, `tools/mutation_report.py`, `tools/mutation_routes.py`:
  the C++ lane, the shapes the lanes share, the kill-route census
- `docs/operations/STABILITY.md` — sibling opt-in lane
- `docs/development/CI_LOCAL.md` — three-layer CI architecture
