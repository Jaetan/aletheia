# Mutation Testing — operations guide

R18 cluster 7 wires mutation testing across all three bindings.
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

The static gate (`tools/check_mutation_setup.py`) runs always-on as step
13 of `tools/run_ci.py`; it fires when a hot-path source file is renamed
or deleted without updating the YAML.  The dynamic runner is opt-in via
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
| Python | `mutmut` 3.x | `aletheia/client/_client.py`, `aletheia/dbc_converter.py`, `aletheia/yaml_loader.py`, `aletheia/validation.py`, `aletheia/protocols.py` |
| Go | `gremlins` | `aletheia/client.go`, `dbc.go`, `json.go`¹, `ffi.go`, `ffi_nocgo.go`, `enrich.go`² |
| C++ | `Mull` 0.33.0 (LLVM 19) | `cpp/src/*.cpp` (full set, mock_backend.cpp + types.cpp excluded as test/type-defs) |

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

Mull is installed locally to `~/.local/bin/` (no sudo).  The Mull-19
release matches the LLVM-19 toolchain installed via the standard Debian
apt repo (`apt install clang-19`).  The next major Mull release will be
Mull-20 ↔ clang-20; pin to whichever pair is present locally.

```bash
# Download the LLVM-19 deb from the Mull GitHub release (~32 MB).
curl -fsSLO https://github.com/mull-project/mull/releases/download/0.33.0/Mull-19-0.33.0-LLVM-19.1.7-debian-amd64-13.deb

# Local extract (no sudo) — mull binaries land in ~/.local/bin/, which
# the project assumes is on $PATH (see CLAUDE.md § Development Environment).
mkdir -p /tmp/mull-extract
dpkg-deb -x Mull-19-0.33.0-LLVM-19.1.7-debian-amd64-13.deb /tmp/mull-extract
cp /tmp/mull-extract/usr/bin/mull-runner-19 ~/.local/bin/
cp /tmp/mull-extract/usr/bin/mull-reporter-19 ~/.local/bin/
cp /tmp/mull-extract/usr/lib/mull-ir-frontend-19 ~/.local/bin/

# Verify
mull-runner-19 --version    # expect: mull-runner 0.33.0  LLVM: 19.1.7
```

clang-19 is required for the IR pass:

```bash
sudo apt install clang-19   # provides /usr/bin/clang-19, /usr/bin/clang++-19
```

The standard build (`cmake -B build`) keeps using whatever `clang++` /
`g++` is on `$PATH`; the mutation lane uses `clang++-19` only inside its
dedicated `cpp/build-mutation/` tree (set via `-DCMAKE_CXX_COMPILER=clang++-19`).

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

# C++
cd cpp
cmake -B build-mutation -DALETHEIA_MUTATION=ON \
      -DCMAKE_C_COMPILER=clang-19 -DCMAKE_CXX_COMPILER=clang++-19
cmake --build build-mutation --target unit_tests
mull-runner-19 ./build-mutation/unit_tests
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
| Static gate (`check-mutation-setup`) | Every push (via pre-push hook) | <1 sec | Always-on, step 13 of `run_ci.py` |
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
- `docs/operations/STABILITY.md` — sibling opt-in lane (R18 cluster 6)
- `docs/development/CI_LOCAL.md` — three-layer CI architecture
- `memory/feedback_orchestrator_end_to_end_validation.md` — forward-revert protocol
