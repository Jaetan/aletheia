## CI/CD (5 categories)

Scope: ALL files in `.github/workflows/`, `.github/actions/`, plus any cron/scheduled-job configuration files, release-pipeline scripts under `tools/release/`, and the Shake build targets that ship to release lanes (`Shakefile.hs` `dist`/`install`/`release` rules). The CI/CD configuration is part of the supply chain — review with the same rigor as production code. A workflow YAML that silently masks a failed test produces a false green build; a misconfigured cache poisons every downstream build until detected. CI/CD findings block release.

**Tooling gates (hard requirements):**
- `actionlint` must produce **zero findings** on every workflow YAML in `.github/workflows/`.
- Every external action reference uses a 40-character commit SHA, never a tag (`@v3`, `@v4.0.1`) or branch (`@main`); a `dependabot.yml` config raises PRs to bump SHAs and the bump is reviewed like any other dependency change.
- **Adding any `continue-on-error: true` or `|| true`-style mask** requires a written rationale comment naming the failure mode and the recovery path — without a rationale, the silent-failure surface is a finding.

### Hygiene & Hardening (5)

1. **Workflow YAML hygiene** -- `actionlint` clean. Every action pinned by 40-char commit SHA. Runner OS+version pinned (`ubuntu-24.04`, never `ubuntu-latest` — silent runner upgrades have produced regressions in adjacent projects; the project must own the upgrade window). No `|| true` masking failures. No `continue-on-error: true` without a written rationale comment naming the failure mode. Multi-step `run:` blocks use `set -euo pipefail` (or `bash -e`) at the top — bare `run: |` lets earlier-line failures pass silently because GitHub Actions only checks the final exit code. `if: always()` on cleanup steps; `if: failure()` on diagnostic-collection steps; never bare `if:` evaluating a non-boolean.
2. **Cache discipline** -- cache keys hash all inputs (lockfiles + workflow file SHA + tool versions + matrix-cell identifier); a key that excludes the workflow file is a finding because workflow edits silently reuse poisoned caches. No overlap with adjacent jobs that would write/read the same key cross-purpose. Explicit cache size caps where the runner has limits (GitHub-hosted: 10 GB per repo). `restore-keys` ordered most-specific-first; the catch-all key is documented as "cold start acceptable, never a correctness fallback." Cache misses are reported in the build summary, not silently absorbed.
3. **Permission scoping** -- every workflow has an explicit `permissions:` block at workflow or job level. The default is `contents: read` (or `permissions: {}` on jobs that need none); write permissions are granted only on the smallest scope that needs them (`pull-requests: write` on the autocomment job, never blanket on the build job). `GITHUB_TOKEN` not echoed, not passed through `set-output`/`$GITHUB_OUTPUT`. Secrets (`${{ secrets.X }}`) accessed only inside steps that need them, never piped through environment variables exposed to logs. Third-party actions running on PRs from forks use `pull_request_target` only with explicit understanding of the privilege escalation risk and a written rationale.
4. **Build-vs-test isolation** -- build jobs do not depend on test jobs and vice versa where the dependency is artificial; matrix builds are independent across cells. `fail-fast: true` only when matrix members are equivalent (a partial-failure run produces no useful information when cells are independent). No shared mutable state via cache between matrix cells of different language versions, OS versions, or platforms — that is the canonical CI flake source. Per-cell working directories isolated; concurrent jobs that write to the same artifact path are findings.
5. **Artifact and release surface** -- `actions/upload-artifact` retention explicitly set per artifact class (build artifacts: 7-14 days; release artifacts: 90 days or longer per release policy; debug artifacts: 1-3 days). Release-build path documented in `docs/development/RELEASE.md` (or equivalent) with the exact workflow file and target. Signed artifacts (Sigstore / cosign) where the toolchain supports it; an unsigned release artifact is acceptable only with a written justification in the release doc. SBOM (CycloneDX or SPDX) generated per release — the SBOM is the audit trail for the GHC/cabal/Agda toolchain pin and the LGPL-contingency `--bignum=native` rebuild verification (Universal Rules → "Reproducible build verification"). Reproducible-build hash recorded per release artifact and compared against a second clean build; drift is a finding.

### Verification

```bash
# actionlint must be installed locally for the workflow-YAML gate
actionlint .github/workflows/*.yml .github/workflows/*.yaml
# Pin-by-SHA gate (audit script); the script's absence is itself a CI/CD cat 1 finding:
tools/check_action_pins.py
# Permission-scoping gate; same — script absence is a finding:
tools/check_workflow_permissions.py
# Reproducible-build hash diff (Universal Rules cross-reference):
tools/check_reproducible_build.py
```

All three audit scripts and `.github/dependabot.yml` are in place (added 2026-05-09).  Subsequent rounds maintain them: R20 surfaced regex-hardening and edge-case findings against the scripts themselves (`CICD-1.2`, `CICD-1.3`, `CICD-2.3`, `CICD-3.2`, `CICD-5.1`) — open work, tracked in the round's findings doc.  Action references in `.github/workflows/` are still tag-pinned (`@v4`) rather than 40-char SHA; the SHA-migration is the next reviewable change under cat 1 and remains in the queue until Dependabot raises and lands the migration PRs.

---

