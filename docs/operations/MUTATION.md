# Mutation Testing — operations guide

Mutation testing runs across all three bindings.
The actual tools are: **Python** via `mutmut`, **Go** via `gremlins`
(substituted for the AGENTS.md cat 14(g)–named `go-mutesting`, which is
unmaintained — see § Per-binding sub-checks), **C++** via `Mull`.  This doc
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
benchmarks/mutation/<short-sha>/   Per-commit JSON + raw tool logs (gitignored)
```

The static gate (`tools/check_mutation_setup.py`) runs always-on
(`check-mutation-setup`) in `tools/run_ci.py`; it fires when a hot-path
source file is renamed or deleted without updating the YAML.  The dynamic runner is opt-in via
`ALETHEIA_MUTATION_CHECK=1` or `tools/run_ci.py --mutation`.

## Threshold model

Two-tier per advisor 2026-05-09:

- **Drift gate (hard equality)** — observed survivor count must not exceed
  the baseline recorded in `docs/MUTATION_BENCH.yaml`.  Any new survivor is
  a finding, surfaced via the runner's exit code = 1 with a JSON report
  pointing at the file/line.
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
| Go | `gremlins` | `aletheia/client.go`, `dbc.go`, `json.go`¹, `ffi.go`, `ffi_nocgo.go`, `enrich.go`² |
| C++ | `Mull` 0.34.0 (LLVM 22, from source) | `cpp/src/*.cpp` less `mock_backend.cpp` / `types.cpp` (test-only / type-defs) and `rational_renderer.cpp` — the exact mutated set is enumerated in `docs/MUTATION_BENCH.yaml` |

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
.venv/bin/mutmut --version    # expect: mutmut, version 3.5.0 (or later 3.x)
```

The `[mutation]` extras section in `pyproject.toml` pins `mutmut>=3.5,<4`
— major-version pin is intentional because mutmut 3.x added the trampoline
machinery; the 2.x → 3.x transition broke `[tool.mutmut]` semantics.

### Go — `gremlins`

```bash
go install github.com/go-gremlins/gremlins/cmd/gremlins@latest
which gremlins    # expect: ~/go/bin/gremlins
```

`~/go/bin` should already be in `$PATH` — verify with `echo $PATH`.

(Per the table above, `gremlins` substitutes for the AGENTS.md-named
`go-mutesting`; both reach the same operator set.)

### C++ — `Mull`

The project supports only the latest stable Clang (22), and UB can differ
between compiler versions — so the mutation lane MUST test clang-22 codegen.
No prebuilt Mull deb ships for LLVM 22 (Mull's release debs stop at LLVM-15),
so Mull is **built from source** against the system LLVM-22.  The binaries
land in `~/.local/bin/` (no sudo for the copy), which the project assumes is
on `$PATH` (see CLAUDE.md § Development Environment).

```bash
# System LLVM-22 + clang-22 (one-time; apt.llvm.org on Debian/Ubuntu).
sudo apt install clang-22 llvm-22-dev libclang-22-dev

# Build Mull 0.34.0 from source.  bazelisk reads Mull's .bazelversion (8.6.0);
# the build uses the system LLVM via new_local_repository(/usr/lib/llvm-22) —
# no LLVM download.
curl -fsSL -o ~/.local/bin/bazel \
  https://github.com/bazelbuild/bazelisk/releases/download/v1.27.0/bazelisk-linux-amd64
chmod +x ~/.local/bin/bazel
git clone --depth 1 --branch 0.34.0 --recursive \
  https://github.com/mull-project/mull /tmp/mull
cd /tmp/mull
# Mull's MODULE.bazel OS map caps ubuntu:24.04 at LLVM-20 — add "22":
sed -i 's/        "ubuntu:24.04": \[/        "ubuntu:24.04": [\n            "22",/' MODULE.bazel
bazel build //rust/mull-tools:mull-runner-22 \
            //rust/mull-tools:mull-reporter-22 //:mull-ir-frontend-22
cp -L bazel-bin/rust/mull-tools/mull-runner-22   ~/.local/bin/
cp -L bazel-bin/rust/mull-tools/mull-reporter-22 ~/.local/bin/
cp -L bazel-bin/mull-ir-frontend-22              ~/.local/bin/

# Verify
mull-runner-22 --version    # expect: mull-runner 0.34.0  LLVM: 22.x
```

`mull-runner` / `mull-reporter` are Rust binaries; `mull-ir-frontend-22` is a
C++ clang plugin `.so`.  The standard build (`cmake -B build`) also requires
`clang++-22` (the project supports the latest stable Clang only; g++
unsupported); the mutation lane uses the same `clang++-22` inside its dedicated
`cpp/build-mutation/` tree.  CI caches both the clang-22 debs and the
from-source Mull build (keyed on the Mull tag + LLVM version) — see
`.github/workflows/pr-heavy-lanes.yml`.

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

# C++ (needs build/libaletheia-ffi.so — the ALETHEIA_MUTATION build folds the
# real-.so integration tests into unit_tests to cover FfiBackend, so run
# `cabal run shake -- build` first).
cd cpp
cmake -B build-mutation -DALETHEIA_MUTATION=ON \
      -DCMAKE_C_COMPILER=clang-22 -DCMAKE_CXX_COMPILER=clang++-22
cmake --build build-mutation --target unit_tests
mull-runner-22 ./build-mutation/unit_tests
```

Per-binding skip env vars (useful for partial runs):

```bash
ALETHEIA_MUTATION_SKIP_PYTHON=1   # skip Python lane only
ALETHEIA_MUTATION_SKIP_GO=1       # skip Go lane only
ALETHEIA_MUTATION_SKIP_CPP=1      # skip C++ lane only
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
   AGENTS.md "an unjustified survivor is a test gap").
3. Re-running the lane to confirm no regression.

A baseline IMPROVEMENT (observed < baseline) is permitted to land via the
same YAML edit pattern; the new lower count becomes the floor.

## Forward-revert verification protocol

Per `feedback_orchestrator_end_to_end_validation.md`, every gate's
shape is verified by injecting a violation and confirming the gate fires
with a precise diagnostic.

### Static gate (`tools/check_mutation_setup.py`)

```bash
# Inject violation: rename a hot-path entry in YAML to a non-existent path.
sed -i 's|aletheia/client/_client.py|aletheia/client/_NONEXISTENT.py|' \
    docs/MUTATION_BENCH.yaml
python3 tools/check_mutation_setup.py
# Expect: exit 1 with diagnostic naming the missing path.

# Restore.
git checkout docs/MUTATION_BENCH.yaml
python3 tools/check_mutation_setup.py
# Expect: exit 0 with "20 hot-path sources all present".
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
without YAML update — catches the same drift class as
`feedback_module_count_prose_audit.md` but for hot-path file paths.  The
dynamic gate is the actual mutation pass; per AGENTS.md "once per PR is
sufficient; per-commit is overkill".

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

- `AGENTS.md` cat 14(g) (Python / Go / C++) — canonical hot-path lists
- `docs/MUTATION_BENCH.yaml` — actual on-disk paths, baseline numbers
- `tools/check_mutation_setup.py` — static gate (always-on)
- `tools/mutation_run.py` — dynamic runner (opt-in)
- `docs/operations/STABILITY.md` — sibling opt-in lane
- `docs/development/CI_LOCAL.md` — three-layer CI architecture
- `memory/feedback_orchestrator_end_to_end_validation.md` — forward-revert protocol
