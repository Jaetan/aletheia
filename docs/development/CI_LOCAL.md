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
| Offline correctness sweep | `tools/run-ci.sh` | `git push` (via pre-push hook) | 17-step gate sweep — Agda gates, binding tests, lints |
| Push-time meta-gates | `.github/workflows/*.yml` | `git push origin <branch>` to GitHub | Action-pin / workflow-permissions / actionlint — verifies the GHA infrastructure itself |
| Local GHA-replay | `act` + `.actrc` | manual `act <event>` | Run the GHA workflows offline before push to catch breakage before consuming Actions minutes |

The pre-push hook (`tools/install-hooks.sh`) is the principal correctness
gate; the GHA workflows are intentionally narrow.

## Offline correctness sweep — `tools/run-ci.sh`

Documented in [`tools/run-ci.sh`](../../tools/run-ci.sh). 17 sequential
steps, ~12-15 minutes warm. Logs to `tools/ci-output/ci-<branch>-<timestamp>.log`
for use as falsifiable gate-claim-integrity evidence.

Install the pre-push hook:

```bash
tools/install-hooks.sh
```

Idempotent (safe to re-run). After install, every `git push` runs the sweep
before allowing the push. Bypass with `git push --no-verify` for incident
response.

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
high-stakes external PRs, run `tools/run-ci.sh` locally on the merged branch
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
pushing. The pre-push hook (`tools/run-ci.sh`) does NOT invoke `act`
automatically because `act` requires Docker, which not every dev environment
provides; treat `act` as an opt-in workflow-development tool.

For a CI-style local replay, run both:

```bash
tools/run-ci.sh    # correctness gates (17 steps, ~12-15 min)
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

The pre-push hook runs the full 17-step sweep (~12-15 min). If you need to
push iteratively (e.g., a doc-only fix that doesn't affect gates), bypass
with:

```bash
git push --no-verify
```

Only bypass when you understand why — the hook is the principal correctness
gate. The gate-claim-integrity enforcer (`tools/check-gate-claim.sh`) still
validates the .so freshness invariant on commits with "all gates clean"
assertions, even if the pre-push hook didn't run.

## See also

- [`tools/run-ci.sh`](../../tools/run-ci.sh) — offline correctness orchestrator (Phase 3).
- [`tools/install-hooks.sh`](../../tools/install-hooks.sh) — pre-push hook installer.
- [`tools/check-changelog.sh`](../../tools/check-changelog.sh) — UR-1 enforcement (Phase 1).
- [`tools/check-gate-claim.sh`](../../tools/check-gate-claim.sh) — gate-claim integrity (Phase 2).
- [`memory/feedback_gate_claim_integrity.md`](../../../.claude/projects/-home-nicolas-dev-agda-aletheia/memory/feedback_gate_claim_integrity.md) — the discipline this enforces.
