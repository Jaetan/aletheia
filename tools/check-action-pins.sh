#!/usr/bin/env bash
# tools/check-action-pins.sh — Verify action-pin policy on GHA workflows.
#
# Aletheia's action-pin policy:
#   * GitHub-owned actions (actions/*, github/*) — `@v<n>` tag accepted.
#     These are first-party, less risk of supply-chain compromise; tags are
#     stable enough.
#   * All other actions — must be SHA-pinned (40-char hex commit hash) to
#     defend against supply-chain attacks where a tag is moved to a
#     malicious commit.
#
# Reference: GitHub Security Hardening for GitHub Actions (Sept 2022),
# advisory after the tj-actions/changed-files compromise.
#
# Runs as both:
#   * Offline (pre-push hook via tools/run-ci.sh, manual invocation).
#   * Push-time (GHA workflow .github/workflows/gha-checks.yml).
#
# Exit codes:
#   0 — all `uses:` references comply with the pin policy.
#   1 — at least one `uses:` reference violates the policy.
#   2 — no .github/workflows/ directory (skips silently with exit 0).

set -euo pipefail

repo_root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  echo "check-action-pins: not inside a git repo" >&2
  exit 2
}
cd "$repo_root"

workflows_dir=".github/workflows"
if [ ! -d "$workflows_dir" ]; then
  echo "check-action-pins: $workflows_dir does not exist; skipping"
  exit 0
fi

violations=""
checked=0

# Iterate over each workflow file.
while IFS= read -r workflow; do
  [ -z "$workflow" ] && continue
  while IFS= read -r line; do
    # Match `uses:` references.  Format: `uses: <repo>@<ref>` where <repo>
    # is `owner/name` or `owner/name/path`, and <ref> is a tag, branch, or SHA.
    if [[ "$line" =~ uses:[[:space:]]*([^[:space:]@]+)@([^[:space:]]+) ]]; then
      repo="${BASH_REMATCH[1]}"
      ref="${BASH_REMATCH[2]}"
      checked=$((checked + 1))

      # Strip "./" or "docker://" prefix references — those aren't
      # third-party actions.
      if [[ "$repo" == ./* ]] || [[ "$repo" == docker://* ]]; then
        continue
      fi

      # Allowlist: GitHub-owned orgs (actions/*, github/*).
      if [[ "$repo" == actions/* ]] || [[ "$repo" == github/* ]]; then
        # Tag is acceptable.  Reject branch refs (e.g., @main, @master).
        if [[ "$ref" =~ ^(main|master|develop|HEAD)$ ]]; then
          violations+="  $workflow: $repo@$ref (branch ref disallowed even for github-owned)"$'\n'
        fi
        continue
      fi

      # Third-party actions — must be SHA-pinned (40-char hex).
      if [[ ! "$ref" =~ ^[a-f0-9]{40}$ ]]; then
        violations+="  $workflow: $repo@$ref (third-party — must be SHA-pinned, not tag/branch)"$'\n'
      fi
    fi
  done < "$workflow"
done < <(find "$workflows_dir" -maxdepth 1 -type f \( -name '*.yml' -o -name '*.yaml' \))

if [ -n "$violations" ]; then
  cat >&2 <<EOF
check-action-pins: FAIL — action-pin policy violations detected.

Pin policy:
  * GitHub-owned (actions/*, github/*) — @v<n> tag accepted (no branch refs)
  * Third-party — must be SHA-pinned (40-char hex)

Violations ($checked refs checked):
$violations
Fix: replace tag refs with the underlying SHA.  Look up via:
  gh api repos/<owner>/<name>/git/ref/tags/<tag> --jq .object.sha

Reference: GitHub Security Hardening for GitHub Actions.
EOF
  exit 1
fi

echo "check-action-pins: ok ($checked refs checked, all comply with pin policy)"
