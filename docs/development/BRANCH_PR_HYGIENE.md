<!--
SPDX-FileCopyrightText: 2025 Nicolas Pelletier
SPDX-License-Identifier: BSD-2-Clause
-->

# Branch & PR hygiene — server-side gate enforcement (DEFERRED / TO REVISIT)

> **Status: deferred.** This is a plan to revisit, not active infrastructure.
> The workflow below is an **untested v1 draft** — well-formed and policy-
> compliant, but never run in real GitHub Actions. Do **not** turn on branch
> protection until the workflow is green on a real PR.

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

1. Commit the workflow (below) — it does **nothing** until step 4.
2. Push it on a branch; read the red; fix the toolchain setup; **iterate to
   green**. You cannot test a GHA workflow without committing + pushing it.
3. Only once it is **green on a real PR**:
4. Repo settings → Branches → protect `main`: *Require status checks to pass*
   → select this job; *Require a pull request before merging*; *Do not allow
   bypassing*. (Marking it required while red would block every merge.)

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

## The draft workflow

Drop this into `.github/workflows/pr-full-ci.yml` when enabling. It passes the
repo's own `check_action_pins` + `check_workflow_permissions` meta-gates
(ghcup is used directly so there is no third-party action to SHA-pin; a
read-only `permissions:` block is declared).

```yaml
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# ⚠️ UNTESTED v1 DRAFT — server-side full correctness sweep for PR enforcement.
# See docs/development/BRANCH_PR_HYGIENE.md. Pair with branch protection
# (require this check + block direct pushes to main) ONLY once green on a PR.

name: Full CI sweep (PR enforcement)

on:
  pull_request:
  push:
    branches: [main]

permissions:
  contents: read

concurrency:
  group: full-ci-${{ github.ref }}
  cancel-in-progress: ${{ github.event_name == 'pull_request' }}

jobs:
  full-sweep:
    name: tools/run_ci.py (all gates)
    runs-on: ubuntu-24.04
    timeout-minutes: 120
    env:
      GHC_VERSION: '9.6.7'
      AGDA_VERSION: '2.8.0'
      STDLIB_VERSION: 'v2.3'
    steps:
      - name: Checkout (full history)
        uses: actions/checkout@v6
        with:
          fetch-depth: 0

      - name: Ensure a local `main` ref for `git diff main...HEAD`
        run: git fetch --no-tags origin +refs/heads/main:refs/heads/main || true

      - name: Set up GHC + cabal
        run: |
          set -euo pipefail
          ghcup install ghc "${GHC_VERSION}" --set
          ghcup install cabal 3.12.1.0 --set
          cabal update
          echo "${HOME}/.cabal/bin" >> "${GITHUB_PATH}"
          echo "${HOME}/.ghcup/bin" >> "${GITHUB_PATH}"

      - name: Cache cabal store (Agda library + deps)
        uses: actions/cache@v4
        with:
          path: |
            ~/.cabal/store
            ~/.cabal/packages
          key: cabal-${{ runner.os }}-ghc${{ env.GHC_VERSION }}-agda${{ env.AGDA_VERSION }}

      - name: Install Agda ${{ env.AGDA_VERSION }} (binary + store library)
        run: cabal install "Agda-${AGDA_VERSION}" --overwrite-policy=always

      - name: Cache agda-stdlib ${{ env.STDLIB_VERSION }}
        uses: actions/cache@v4
        with:
          path: ~/.agda/agda-stdlib
          key: agda-stdlib-${{ env.STDLIB_VERSION }}

      - name: Install + register agda-stdlib ${{ env.STDLIB_VERSION }}
        run: |
          set -euo pipefail
          mkdir -p ~/.agda
          if [ ! -d ~/.agda/agda-stdlib/.git ]; then
            git clone --depth 1 --branch "${STDLIB_VERSION}" \
              https://github.com/agda/agda-stdlib.git ~/.agda/agda-stdlib
          fi
          echo "${HOME}/.agda/agda-stdlib/standard-library.agda-lib" > ~/.agda/libraries
          echo "standard-library" > ~/.agda/defaults

      - name: Set up Python 3.14
        uses: actions/setup-python@v5
        with:
          python-version: '3.14'

      - name: Create the dev venv (python/.venv)
        run: |
          set -euo pipefail
          python3.14 -m venv python/.venv
          python/.venv/bin/pip install --upgrade pip
          python/.venv/bin/pip install -e 'python/.[dev]'

      - name: Set up Go
        uses: actions/setup-go@v5
        with:
          go-version: 'stable'

      # ⚠️ FRAGILE: ubuntu-24.04 defaults to gcc-13/clang-18; the build wants
      # g++>=14 / clang>=21 and clang-tidy + ubsan use clang-19. If clang-19 is
      # not in the default apt on the runner, add apt.llvm.org. Adjust on red runs.
      - name: Install C++ toolchain (cmake, g++-14, clang-19 + tidy/format)
        run: |
          set -euo pipefail
          sudo apt-get update
          sudo apt-get install -y cmake g++-14 clang-19 clang-tidy-19 clang-format-19
          sudo update-alternatives --install /usr/bin/clang        clang        /usr/bin/clang-19        100
          sudo update-alternatives --install /usr/bin/clang++      clang++      /usr/bin/clang++-19      100
          sudo update-alternatives --install /usr/bin/clang-tidy   clang-tidy   /usr/bin/clang-tidy-19   100
          sudo update-alternatives --install /usr/bin/clang-format clang-format /usr/bin/clang-format-19 100

      - name: Run the full offline correctness sweep (tools/run_ci.py)
        run: python/.venv/bin/python3 -m tools.run_ci
```
