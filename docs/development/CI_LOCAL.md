# Local CI: offline gate enforcement and `act` Docker pairing

Aletheia's CI architecture is **local-first**: the full correctness sweep runs
on dev machines via the pre-push hook, while `.github/workflows/` is reserved
for push-time-unique gates that have no offline equivalent (action-pin
verification, workflow-permissions hygiene, dependabot scans). This document
explains the two pieces and how they fit together.

The architecture is motivated by the limited GitHub Actions monthly allotment
on private repositories. By moving correctness validation offline, the
repository can absorb most pre-push iteration cost without consuming GHA
minutes.

## Architecture at a glance

| Layer | Lives in | Triggered by | Coverage |
|---|---|---|---|
| Pre-commit gate | `tools/run_ci.py --fast` + `tools/iwyu.py --check --wait-lock` (via pre-commit hook) | `git commit` | The compile-free FAST tier on the staged content, then the IWYU `.agdai`-reader scan (named + wildcard) on staged `.agda` files; blocks on any failure or finding |
| Offline correctness sweep | `tools/run_ci.py` (via pre-push hook) | `git push` | **The always-on gate sweep** — Agda gates (the proof/invariant/erasure/fidelity/export checks fold into one `cabal run shake` call; build is a separate prereq; + the IWYU gate + its self-test on branch-modified files), offline enforcers, binding tests, lints, GHA meta-checks (+ 4 opt-in lanes) |
| Push-time meta-gates | `.github/workflows/*.yml` | `git push origin <branch>` to GitHub | Action-pin / workflow-permissions / actionlint — verifies the GHA infrastructure itself |
| Local GHA-replay | `act` + `.actrc` | manual `act <event>` | Run the GHA workflows offline before push to catch breakage before consuming Actions minutes |

The pre-push hook (installed by `tools/install_hooks.py`) is the principal
correctness gate; the GHA workflows are intentionally narrow.

## Pre-commit hook (blocking) — `tools/run_ci.py --fast` + `tools/iwyu.py --check`

The hook first runs the compile-free FAST tier of the sweep on the staged
content (unstaged and untracked changes are stashed for the duration and
restored after) and refuses the commit on any failure.  It then runs the
single scope-aware `.agdai` IWYU tool against staged `.agda` files under
`src/`.  Any finding (dead / redundant / narrowable / unresolved import)
refuses the commit, and so does a run that never reached a verdict: a
non-zero exit with no report is reported as a check the hook did not get,
with the tool's own output above it, never as findings.  The tool is run
with `--wait-lock`, so a commit made while another Agda tool holds the
agda-tree lock (a proof sweep, another IWYU run) waits for it, saying so
with the holder's pid, rather than being refused or waved through.

It is not sub-second (it warm-loads the staged files to refresh their
`.agdai` interfaces), so it runs only when `.agda` files are staged.  The
reader reads interfaces directly — no recompile-confirm — and its
verdicts are validated by the synthetic fixture matrix
(`tools/iwyu.py --self-test`), so there is no false-positive ignore list
to maintain.  The same gate runs blocking at pre-push.

## Offline correctness sweep — `tools/run_ci.py`

Documented in [`tools/run_ci.py`](../../tools/run_ci.py). The always-on
sequential steps run ~22-30 minutes warm (both sanitizer ctest lanes are
always-on, not opt-in: an opt-in sanitizer lane can let a defect — UB, as in
`Rational::from_double`, or a read of a returned frame, as in the serializer
depth-bound test — ship undetected; the IWYU gate + its self-test is the
dead-import gate).
`run_ci` prints each step as `[i/N]` at runtime, so the live count is
authoritative.
Plus 4 opt-in lanes (reproducible build, stability bench, mutation
testing, coverage floors) that can be enabled individually via CLI flags or env vars,
or all at once via `--full`.  Logs to
`tools/ci-output/ci-<branch>-<timestamp>.log`.  The log's header records a
digest of the build sources the sweep observed (the Agda sources, the
Shakefile, the Haskell shim and the library file, keyed by git's own blob ids,
so a checkout that rewrites every mtime leaves it unchanged), and the summary
re-measures it: a sweep whose build sources moved while it ran fails rather
than vouch for a tree no step is known to have observed.  A passed log is the
falsifiable evidence behind a "gates clean" claim, and `tools/check_gate_claim.py`
reads it by that digest.  A `--fast` sweep runs a subset and records no digest.
Every step runs in a process group of its own under a guard that interrupts it
when the sweep dies, however it dies, and Ctrl-C stops the running steps before
the sweep exits, so an ended sweep leaves no build holding Shake's lock.

### The build prerequisite and the staleness gate

The sweep's first step builds `libaletheia-ffi.so` — but *which* build runs
depends on `--build-staleness {auto,always,never}` (default `auto`):

- **`auto`** — run the staleness gate (`tools/check_build_incremental.py`) when
  the diff vs the local `main` touches a build-graph file (`Shakefile.hs`,
  `shake.cabal`, `aletheia.agda-lib`, `haskell-shim/`,
  `tools/check_build_incremental.py`, `tools/_warm.py`); otherwise a plain
  `cabal run shake -- build`.  Fails **safe**: if the diff can't be computed
  (e.g. no local `main` ref) the gate runs rather than silently skip a safety
  check.  A code-only branch thus skips the ~260s of staleness relinks; a branch
  that touches the build graph pays for them.
- **`always`** — always run the staleness gate.  The `push:main` CI job uses this
  (`pr-full-ci.yml` passes `--build-staleness=always` on `push`), re-verifying
  the no-stale-`.so` invariant on every landing.
- **`never`** — always a plain build.

The staleness gate is a *behavioral* regression test that the honest dependency
graph (see [BUILDING.md → Incremental Builds](BUILDING.md#incremental-builds))
stays correct.  It mutates real runtime string literals in two structurally
distant modules, rebuilds, and checks two properties:

1. **Never stale** — an edit to a runtime literal must REACH the `.so` (and a
   revert must too).  This is the failure the old `rm -rf` sledgehammer masked by
   always full-rebuilding.
2. **Incremental** — a no-op build must NOT relink the `.so` (its mtime stays
   put).  A regression back to the sledgehammer would pass property 1 but fail
   here.

Every edited source is restored on exit, on SIGINT and on SIGTERM.  SIGKILL
bypasses that and leaves the run's marker in the two sources.  The build runs
in a process group of its own under a guard that interrupts it when the gate
dies, however it dies, so a killed run leaves no build behind.  The marker
names the run that wrote it, so the next gate run refuses before it builds and
says which run was interrupted, whether it still lives, and the edit that
restores the file; it also refuses while a build holds Shake's lock, naming
that process.  The gate holds the repo-wide Agda lock for its whole body, so a
second run started over a first reports the lock as held instead of capturing
the first run's edit as its own original.

The IWYU gate (`tools/iwyu.py --check --diff`) runs on the set
of `.agda` files modified vs `main` (`git diff main...HEAD -- src/`; empty
diff ⇒ no-op).  In one warm process it judges BOTH named imports
(`using`/`renaming` → DEAD/UNRESOLVED) and wildcard `open import M`
(DEAD / REDUNDANT / NARROWABLE) via the scope-aware `.agdai` reader, and
fails on any finding (UNRESOLVED is surfaced, never silently passed).
Its self-test (`tools/iwyu.py --self-test`) validates that reader against the
synthetic fixture matrix (its correctness gate, replacing the retired
recompile oracle).  Neither recompiles; the gate reads interfaces directly
and runs on every scoped file (no file-count skip).  Cross-file deadness (a name made dead by an
edit in an UNCHANGED file) is caught by the periodic whole-tree
(`--all`) run.

Install both hooks (pre-commit + pre-push):

```bash
tools/install_hooks.py
```

Idempotent (safe to re-run; preserves any existing hooks by backing them
up).  After install, every `git commit` runs the FAST tier and the IWYU
gate on the staged content, and every `git push` runs the full always-on
sweep; all of it blocking.
Bypass either hook with `--no-verify`:

```bash
git commit --no-verify   # skip the pre-commit FAST tier + IWYU gate
git push   --no-verify   # skip pre-push CI sweep (for incident response)
```

### Opt-in lanes

Each opt-in lane has a CLI flag, an env-var fallback, and a paired
`--no-<lane>` to subtract from `--full`:

| Flag | Env var | Cost | Coverage |
|---|---|---|---|
| `--repro` | `ALETHEIA_REPRO_CHECK=1` | ~10 min | Two-clean-build sha256 verification |
| `--stability` | `ALETHEIA_STABILITY_CHECK=1` | ~5 min | Long-run leak detection across 3 bindings + GHC RTS heap profile |
| `--mutation` | `ALETHEIA_MUTATION_CHECK=1` | ~30 min - 2 hrs | Per-binding mutation testing — mutmut / gremlins / Mull |
| `--coverage` | `ALETHEIA_COVERAGE_CHECK=1` | ~3 min | Per-binding coverage floors — coverage.py / `go test -cover` / llvm-cov / cargo-llvm-cov |

Precedence: **CLI flag > env var > default-off**.  `--full` enables every
opt-in lane; `--no-<lane>` always wins (e.g. `--full --no-mutation` runs
everything except mutation testing).

```bash
# Always-on steps only (default; ~22-30 min, incl. both sanitizer ctest lanes)
tools/run_ci.py

# Two specific opt-in lanes
tools/run_ci.py --stability --repro

# All opt-in lanes (~55-115 min on warm host)
tools/run_ci.py --full

# All opt-ins except mutation (skip the 30-minute lane during iteration)
tools/run_ci.py --full --no-mutation

# Legacy env-var trigger (still supported for back-compat)
ALETHEIA_REPRO_CHECK=1 tools/run_ci.py
```

The mutation lane is most expensive and is per-PR not per-commit; the
other three are per-push-friendly when developers want extra coverage.

### Installing dev tools

The always-on sweep needs no extra tooling beyond what `cabal run shake --
build` already requires.  The opt-in lanes need additional installs.

**UBSan and ASan ctest (always-on, no flag)** — need `clang` for the
`-fsanitize-ignorelist=` flag (which g++ doesn't support).  Most distros'
default `clang` package is sufficient; verify with `clang --version`.  No
extra install if you already use `tools/run_ci.py` for the mutation lane
(the supported clang-23 covers sanitizers too; older clang also works here).
Each lane owns its own build tree, `build-ubsan` and `build-asan`, because
sanitizer flags are not safe to mix in one archive, and each runs the whole
ctest battery.  The ASan lane asks for stack-use-after-return detection by
name, which is the class it reads that nothing else does; its entries that
load `libaletheia-ffi.so` run uninstrumented kernel code, so what it reports
about them concerns this repository's own sources
([CGO_NOTES](../architecture/CGO_NOTES.md#addresssanitizer-asan)).
Both lanes are always-on, not opt-in; if clang is absent the step fails
loudly rather than silently skipping — install clang or run the sweep on a
host that has it.

**Reproducible build lane (`--repro`)** — no extra tools (the gate runs
two clean Shake builds and `sha256sum`s the result).

**Stability bench lane (`--stability`)** — needs Python `psutil` (already
in the project's `[dev]` extras) for the Python harness; Go and C++
harnesses use stdlib facilities only.  Install via:

```bash
cd python && .venv/bin/pip install -e '.[dev]'
```

**Mutation lane (`--mutation`)** — needs three tools (one per binding).
See [`docs/operations/MUTATION.md`](../operations/MUTATION.md) for the
full procedure including baseline-management; quick install:

```bash
# Python: mutmut (~250 KB, pip-installable into the venv)
cd python && .venv/bin/pip install -e '.[mutation]'

# Go: gremlins (Go module installed via `go install`; lands in ~/go/bin)
# AGENTS.md names go-mutesting; gremlins substitutes for the same intent
# because zimmski's repo is unmaintained since 2021 (panics on Go 1.26).
go install github.com/go-gremlins/gremlins/cmd/gremlins@latest

# C++: Mull 0.34.1 built from source against system LLVM-23 by
# tools/build_mull.sh (no prebuilt deb ships past LLVM 15, and Mull itself
# stops at LLVM 22, so the script carries the patch).  The procedure, apt deps
# included, is in docs/operations/MUTATION.md § C++.

# Verify all three are discoverable
which mutmut gremlins mull-runner-23  # mutmut is in python/.venv/bin/
```

**Coverage lane (`--coverage`)** — coverage.py comes with the `[dev]` extras
and Go's tool with Go; the other two are `llvm-profdata-23` and `llvm-cov-23`,
which the clang-23 package carries, and `cargo-llvm-cov` at the version
`docs/COVERAGE_BENCH.yaml` pins, which the runner refuses at any other:

```bash
rustup component add llvm-tools-preview
cargo install cargo-llvm-cov --version 0.8.7 --locked
```

See [`docs/operations/COVERAGE.md`](../operations/COVERAGE.md) for what each
tool measures and how the record is re-taken.

Each tool's absence is detected by the mutation runner and surfaces
as a precise error in the per-binding JSON report; the orchestrator marks
the lane as failed but doesn't crash, so a partial install (e.g.
mutmut+gremlins without Mull) still gets you 2 of 3 binding reports.

## Push-time meta-gates — `.github/workflows/`

The workflows in `.github/workflows/` only run gates that have no offline
equivalent or that need GHA's own infrastructure to be validated:

- Workflow YAML lint (actionlint) — verifies the workflow files themselves.
- Action-pin enforcement — every `uses: org/repo@<ref>` must reference a
  full SHA, not a moving tag.
- Workflow-permissions hygiene — minimal `permissions:` scope per workflow.
- Dependabot scans — pull-request-gated; runs on dependabot's own schedule.

These workflows DO NOT duplicate the correctness sweep from `tools/run_ci.py`.
External-contributor PRs from forks that don't have the pre-push hook
installed are gated only by the meta-gates plus repository review. For
high-stakes external PRs, run `tools/run_ci.py` locally on the merged branch
before merging.

## Local GHA-replay — `act`

[`act`](https://github.com/nektos/act) executes `.github/workflows/*.yml`
locally against Docker-backed runners. Use it to validate workflow changes
before pushing — catches workflow YAML errors, missing dependencies, and
permissions issues without consuming Actions minutes.

### Install

```bash
# Linux / WSL
curl -fsSL https://raw.githubusercontent.com/nektos/act/master/install.sh | sudo bash

# macOS
brew install act

# Verify
act --version
```

`act` requires Docker; verify with `docker run --rm hello-world`.

### Configuration

`/home/nicolas/dev/agda/aletheia/.actrc` (committed) pins the runner image
and architecture:

```
-P ubuntu-latest=catthehacker/ubuntu:act-latest
--container-architecture linux/amd64
```

The `catthehacker/ubuntu:act-latest` image (~5 GB) is the act project's
curated "medium" image — includes most common build tools without the
overhead of the "full" 18-GB image.

### Usage

```bash
# Replay a push event on the current branch
act push

# Replay a pull_request event
act pull_request

# List workflows that would run
act -l

# Dry-run (verify YAML without executing)
act --dryrun

# Specific workflow + job
act -W .github/workflows/lint-actions.yml -j actionlint
```

First run downloads the runner image (~5 GB); subsequent runs reuse it.

### When to run `act`

Run `act` after editing any file under `.github/workflows/` and before
pushing. The pre-push hook (`tools/run_ci.py`) does NOT invoke `act`
automatically because `act` requires Docker, which not every dev environment
provides; treat `act` as an opt-in workflow-development tool.

For a CI-style local replay, run both:

```bash
tools/run_ci.py    # correctness gates (always-on sweep, ~22-30 min warm)
act push           # GHA meta-gates (workflows, ~1-2 min)
```

## Troubleshooting

### `act` fails with "image not found"

Pull the image manually:

```bash
docker pull catthehacker/ubuntu:act-latest
```

### `act` runs but a step fails with "command not found"

The `catthehacker/ubuntu:act-latest` image includes most build tools but not
all. If a workflow needs a tool not in the image (e.g., `agda`), it must
install it explicitly via `apt-get install` or similar. Workflows that
require `agda` / `cabal` should not be added to push-time CI — those are
correctness concerns covered by the offline sweep.

### Apple Silicon: workflows hang or behave oddly

Verify `--container-architecture linux/amd64` is in `.actrc`. Without it,
`act` invokes ARM-native runner images, which may have subtle differences
from GHA's amd64 runners.

### Pre-push hook is slow / blocking work

The pre-push hook runs the full always-on sweep (~22-30 min warm). If you need to
push iteratively (e.g., a doc-only fix that doesn't affect gates), bypass
with:

```bash
git push --no-verify
```

Only bypass when you understand why — the hook is the principal correctness
gate. The gate-claim-integrity enforcer (`tools/check_gate_claim.py`) still
refuses a commit whose message asserts "all gates clean" over build sources no
passed sweep recorded, even if the pre-push hook didn't run.

## See also

- [`tools/run_ci.py`](../../tools/run_ci.py) — offline correctness orchestrator (Phase 3).
- [`tools/install_hooks.py`](../../tools/install_hooks.py) — pre-commit + pre-push hook installer.
- [`tools/iwyu.py`](../../tools/iwyu.py) — the single IWYU tool: `--check` (named + wildcard gate), `--apply` (wildcard narrow/remove), `--self-test` (fixture matrix); `--wait-lock` queues behind a running Agda tool. Pre-commit gate + pre-push gate.
- [`tools/_iwyu.py`](../../tools/_iwyu.py) — its engine (internal): the `.agdai` reader driver + both analyses.
- [`tools/agda-iwyu-reader/`](../../tools/agda-iwyu-reader/) — the Haskell reader (links the prebuilt Agda from the cabal store) + its `test/` fixture matrix.
- [`tools/check_changelog.py`](../../tools/check_changelog.py) — CHANGELOG discipline (public API + build/CI/tooling).
- [`tools/check_gate_claim.py`](../../tools/check_gate_claim.py) — gate-claim integrity: a "gates clean" claim means a sweep observed the build sources the commit carries, read from the sweep's own record and never from a timestamp.
