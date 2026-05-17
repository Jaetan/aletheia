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
| Offline correctness sweep | `tools/run_ci.py` | `git push` (via pre-push hook) | 27 always-on steps — Agda gates, offline enforcers, binding tests, lints, GHA meta-checks (+ 4 opt-in lanes) |
| Push-time meta-gates | `.github/workflows/*.yml` | `git push origin <branch>` to GitHub | Action-pin / workflow-permissions / actionlint — verifies the GHA infrastructure itself |
| Local GHA-replay | `act` + `.actrc` | manual `act <event>` | Run the GHA workflows offline before push to catch breakage before consuming Actions minutes |

The pre-push hook (`tools/install_hooks.py`) is the principal correctness
gate; the GHA workflows are intentionally narrow.

## Offline correctness sweep — `tools/run_ci.py`

Documented in [`tools/run_ci.py`](../../tools/run_ci.py). 29 always-on
sequential steps, ~22-27 minutes warm (UBSan ctest promoted from opt-in
to always-on R21 CPP-SYS-32.2 — UB had previously shipped undetected in
`Rational::from_double` because the lane was opt-in).  Plus 3 opt-in
lanes (reproducible build, stability bench, mutation testing) that can
be enabled individually via CLI flags or env vars, or all at once via
`--full`.  Logs to `tools/ci-output/ci-<branch>-<timestamp>.log` for use
as falsifiable gate-claim-integrity evidence.

Install the pre-push hook:

```bash
tools/install_hooks.py
```

Idempotent (safe to re-run). After install, every `git push` runs the sweep
before allowing the push. Bypass with `git push --no-verify` for incident
response.

### Opt-in lanes

Each opt-in lane has a CLI flag, an env-var fallback, and a paired
`--no-<lane>` to subtract from `--full`:

| Flag | Env var | Cost | Coverage |
|---|---|---|---|
| `--repro` | `ALETHEIA_REPRO_CHECK=1` | ~10 min | Two-clean-build sha256 verification (R18 cluster 3 / UR-3) |
| `--stability` | `ALETHEIA_STABILITY_CHECK=1` | ~5 min | Long-run leak detection across 3 bindings + GHC RTS heap profile (R18 cluster 6) |
| `--mutation` | `ALETHEIA_MUTATION_CHECK=1` | ~30 min - 2 hrs | Per-binding mutation testing — mutmut / go-mutesting / Mull (R18 cluster 7) |

Precedence: **CLI flag > env var > default-off**.  `--full` enables every
opt-in lane; `--no-<lane>` always wins (e.g. `--full --no-mutation` runs
everything except mutation testing).

```bash
# Always-on steps only (default; ~22-27 min, incl. UBSan ctest ~5 min)
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
other two are per-push-friendly when developers want extra coverage.

### Installing dev tools

The always-on sweep needs no extra tooling beyond what `cabal run shake --
build` already requires.  The opt-in lanes need additional installs.

**UBSan ctest (always-on, no flag)** — needs `clang` for the
`-fsanitize-ignorelist=` flag (which g++ doesn't support).  Most distros'
default `clang` package is sufficient; verify with `clang --version`.  No
extra install if you already use `tools/run_ci.py` for the mutation lane
(clang-19 / clang-21 are both fine for sanitizers).  Promoted from opt-in
to always-on R21 CPP-SYS-32.2; if clang is absent the step fails loudly
rather than silently skipping — install clang or run the sweep on a host
that has it.

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

# C++: Mull-19 (matches LLVM 19 / clang-19 from the apt repo).  The deb
# is extracted to ~/.local/bin/ — no sudo needed.
sudo apt install clang-19    # one-time; provides /usr/bin/clang-19
curl -fsSLO https://github.com/mull-project/mull/releases/download/0.33.0/Mull-19-0.33.0-LLVM-19.1.7-debian-amd64-13.deb
mkdir -p /tmp/mull-extract
dpkg-deb -x Mull-19-0.33.0-LLVM-19.1.7-debian-amd64-13.deb /tmp/mull-extract
cp /tmp/mull-extract/usr/bin/mull-runner-19 \
   /tmp/mull-extract/usr/bin/mull-reporter-19 \
   /tmp/mull-extract/usr/lib/mull-ir-frontend-19 ~/.local/bin/

# Verify all three are discoverable
which mutmut gremlins mull-runner-19  # mutmut is in python/.venv/bin/
```

Each tool's absence is detected by `tools/mutation_run.py` and surfaces
as a precise error in the per-binding JSON report; the orchestrator marks
the lane as failed but doesn't crash, so a partial install (e.g.
mutmut+go-mutesting without Mull) still gets you 2 of 3 binding reports.

## Push-time meta-gates — `.github/workflows/`

The workflows in `.github/workflows/` only run gates that have no offline
equivalent or that need GHA's own infrastructure to be validated:

- Workflow YAML lint (actionlint) — verifies the workflow files themselves.
- Action-pin enforcement — every `uses: org/repo@<ref>` must reference a
  full SHA, not a moving tag.
- Workflow-permissions hygiene — minimal `permissions:` scope per workflow.
- Dependabot scans — pull-request-gated; runs on dependabot's own schedule.

These workflows DO NOT duplicate the correctness sweep from `run-ci.sh`.
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
tools/run_ci.py    # correctness gates (27 always-on steps, ~17-22 min warm)
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

The pre-push hook runs the full 27-step always-on sweep (~17-22 min warm). If you need to
push iteratively (e.g., a doc-only fix that doesn't affect gates), bypass
with:

```bash
git push --no-verify
```

Only bypass when you understand why — the hook is the principal correctness
gate. The gate-claim-integrity enforcer (`tools/check_gate_claim.py`) still
validates the .so freshness invariant on commits with "all gates clean"
assertions, even if the pre-push hook didn't run.

## See also

- [`tools/run_ci.py`](../../tools/run_ci.py) — offline correctness orchestrator (Phase 3).
- [`tools/install_hooks.py`](../../tools/install_hooks.py) — pre-push hook installer.
- [`tools/check_changelog.py`](../../tools/check_changelog.py) — UR-1 enforcement (Phase 1).
- [`tools/check_gate_claim.py`](../../tools/check_gate_claim.py) — gate-claim integrity (Phase 2).
- [`memory/feedback_gate_claim_integrity.md`](../../../.claude/projects/-home-nicolas-dev-agda-aletheia/memory/feedback_gate_claim_integrity.md) — the discipline this enforces.
