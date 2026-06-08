<!--
SPDX-FileCopyrightText: 2025 Nicolas Pelletier
SPDX-License-Identifier: BSD-2-Clause
-->

# Branch & PR hygiene — server-side gate enforcement

> **Status: workflow committed (`.github/workflows/pr-full-ci.yml`), branch
> protection NOT yet enabled.** The workflow is well-formed and passes the
> repo's own GHA meta-gates (actionlint, action-pins, workflow-permissions),
> but has not yet run in real GitHub Actions. It is **advisory until** `main`
> branch protection marks it a required check. Do **not** turn on branch
> protection until the workflow is green on a real PR (the C++/LLVM lane is the
> expected first red — see footguns).

## Goal

Guarantee that **no code lands on `main` without passing every gate** — as
*enforcement*, not convention.

## Why the current model doesn't guarantee that

Aletheia's CI is **local-first** (see [CI_LOCAL.md](CI_LOCAL.md)):

- The full 32-step sweep — `tools/run_ci.py`, including the IWYU import gate
  (steps 9-10) — runs in the **pre-push hook** on the contributor's machine.
- GitHub Actions runs only `gha-checks.yml`: three narrow meta-checks
  (actionlint, action-pin policy, workflow-permissions) that need only Python.

The gap: a local Git hook is **bypassable** (`git push --no-verify`) and only
active if the contributor ran `tools/install_hooks.py`. So "all gates passed"
holds *by convention* (trusted contributors), not by server-side enforcement.
The merge decision lives on the contributor's machine, not GitHub's.

## The solution: a required PR check that runs the full sweep server-side

`git push --no-verify` only skips *local* hooks; it cannot skip a **required
status check**, because GitHub itself refuses to merge until that check is
green. Three pieces:

1. A `pull_request` (+ `push: main`) workflow that runs the **same**
   `tools/run_ci.py` — one source of truth, no duplicated gate logic.
2. **Branch protection** on `main`: require that check + "Do not allow
   bypassing" + block direct pushes (everything goes through a PR). This is a
   **repo-admin setting, not code** — and the load-bearing part: the workflow
   enforces nothing until the check is marked required.
3. Keep the local pre-push hook as the fast feedback loop; the PR check is the
   un-bypassable backstop.

**Cost:** one ~30–60 min job. The repo is **public**, so Actions minutes are
free on standard runners. The Agda build dominates a cold run (~15 min); the
cabal-store cache amortizes it to seconds on subsequent runs.

This also aligns with the gate-claim-integrity philosophy: the GHA run log is
falsifiable, server-side evidence the gates ran.

## Rollout order (important)

1. ✅ **Done** — the workflow (`.github/workflows/pr-full-ci.yml`) is committed.
   It is **advisory** (runs, reports, but does not block merges) until step 4.
2. **Push + iterate to green.** Push `ci-speed` and open a PR `ci-speed → main`;
   the `pull_request` trigger fires the sweep. Read the red, fix the toolchain
   setup, push again. You cannot test a GHA workflow without pushing it; expect
   the C++/LLVM lane to go red first (see footguns).
3. Only once the **`tools/run_ci.py (all gates)` check is green on a real PR**:
4. Enable branch protection on `main` (see next section).

## How to protect `main` (repo-admin — you must do this in GitHub)

Branch protection is the **load-bearing** part: the workflow enforces nothing
until GitHub is told the check is *required*. It is a repo setting, not code, so
it cannot live in this repo — only a repo admin (you) can set it. Two ways:

### Via the GitHub web UI

1. Go to **`https://github.com/Jaetan/aletheia/settings/branches`**
   (repo → **Settings** → **Branches**).
2. Under **Branch protection rules**, click **Add branch ruleset** (or "Add
   rule" on the classic UI). Set **Branch name pattern** = `main`.
3. Enable **Require a pull request before merging** (this blocks direct
   `git push` to `main`, so every change goes through a PR + the check).
4. Enable **Require status checks to pass before merging**, then in the search
   box add the check named **`tools/run_ci.py (all gates)`** (the job's `name:`).
   ⚠️ The check only appears in that list **after it has run at least once** —
   that's why step 3 (a green PR run) comes first.
5. Enable **Do not allow bypassing the above settings** (so even admins go
   through the gate — otherwise `--no-verify`'s server-side equivalent, an admin
   override, reopens the hole this is closing).
6. Save.

### Via the `gh` CLI (equivalent, if you prefer)

Run after the check has appeared once (needs an admin token):

```sh
gh api -X PUT repos/Jaetan/aletheia/branches/main/protection \
  -H "Accept: application/vnd.github+json" \
  -f 'required_status_checks[strict]=true' \
  -f 'required_status_checks[contexts][]=tools/run_ci.py (all gates)' \
  -f 'enforce_admins=true' \
  -F 'required_pull_request_reviews=null' \
  -F 'restrictions=null'
```

`required_status_checks.strict=true` = "require branches to be up to date before
merging" (re-runs the gate against the latest `main`); `enforce_admins=true` =
"do not allow bypassing". Verify with
`gh api repos/Jaetan/aletheia/branches/main/protection`.

After this, a `--no-verify` push can still skip the *local* hook, but GitHub
refuses to merge any PR whose `tools/run_ci.py (all gates)` check is not green —
the recurring "a gate that had to run wasn't run" failure becomes structurally
impossible on `main`.

## Known footguns (baked into the draft, but the likely iteration points)

- **C++/LLVM is the #1 risk.** `ubuntu-24.04` defaults to `gcc-13` / `clang-18`,
  but the build targets `g++≥14` / `clang≥21` and the clang-tidy + ubsan lanes
  use `clang-19`. If `clang-19` is not in the runner's default apt, add
  `apt.llvm.org`. Expect this section to go red first.
- **Diff base.** `run_ci`'s IWYU `--diff` and `changed_agda_files` do
  `git diff main...HEAD`; the checkout needs `fetch-depth: 0` **and** a local
  `main` ref (the draft fetches it explicitly) or the import gate silently sees
  zero changed files. On a `push`-to-`main` run, `main...HEAD` is empty so only
  `iwyu --self-test` gates there — fine, because the PR trigger is where it
  actually gates the diff.
- **Cache key** = `{os, GHC 9.6.7, Agda 2.8.0, stdlib v2.3}`; accept a full
  rebuild on miss.

## Open design choice

On the merge path the draft runs IWYU `--diff` (parity with the local pre-push
hook — fast; "complete modulo a periodic `--all`"). To make the merge gate
**airtight against cross-file deadness**, run `--all` instead — but that needs a
small `run_ci` knob (it hardcodes `--diff` today). Default `--diff` matches local.

## Already done (2026-06-06)

While scoping this, a pre-existing bug was found and fixed (`feeac9f`):
`gha-checks.yml` invoked the meta-gate checkers as `python3 tools/check_*.py`,
which `ModuleNotFound`s after the `python -m tools.X` migration (the migration
missed the workflow). The action-pin + permissions meta-gates had therefore been
erroring silently in GHA. Fixed to `python3 -m tools.<check>`.

## The workflow (committed)

The full sweep lives in
[`.github/workflows/pr-full-ci.yml`](../../.github/workflows/pr-full-ci.yml)
(it was the v1 draft formerly inlined here). It runs `tools/run_ci.py` (all
gates) on `pull_request` + `push: main`, installs the toolchain via `ghcup`
directly (no third-party action to SHA-pin), declares a read-only
`permissions:` block, and caches the cabal store + agda-stdlib. It passes the
repo's own GHA meta-gates locally (`actionlint`, `check_action_pins`,
`check_workflow_permissions`) and `check-spdx-headers`. The toolchain steps —
especially the C++/LLVM lane — are the expected iteration points on the first
real PR run (see footguns above).
