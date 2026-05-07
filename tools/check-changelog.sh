#!/usr/bin/env bash
# tools/check-changelog.sh — Enforce CHANGELOG entries on public-API changes.
#
# Invoked as the offline enforcer for R18 Universal Rule UR-1 (Public API
# stability and CHANGELOG discipline).  Runs as a Shake phony (`shake
# check-changelog`) and as a pre-push hook step (Phase 3).
#
# Strategy: branch-level granularity.
#
# 1. Compute merge-base with the comparison ref (default `main`).
# 2. List files changed in HEAD..merge-base.
# 3. If any public-API path is changed, require CHANGELOG.md to be changed too.
#
# Public-API paths are the user-visible surface of each binding.  Test files
# and lowercase-private Go identifiers are excluded by the regex filter.
#
# Exit codes:
#   0 — public-API unchanged, OR public-API changed and CHANGELOG.md changed.
#   1 — public-API changed but CHANGELOG.md not changed.
#   2 — usage error / git failure.
#
# v0 limitations (deliberate; see PROJECT_STATUS.md cluster 1 for v1+ plan):
#   * Presence-of-CHANGELOG-modification is sufficient; the script does NOT
#     verify the change appears under `## [X.Y.Z] — Unreleased`.
#   * Branch-level (not per-commit); a branch with one CHANGELOG commit
#     covers any number of public-API commits.
#   * Path-based; refactors of internal `_helpers.py` that don't change
#     surface still trigger the gate.  Workaround: add a CHANGELOG entry
#     under `### Changed` describing the internal refactor (or `### No
#     change`-style note).

set -euo pipefail

base="${1:-main}"

if ! git rev-parse --verify "$base" >/dev/null 2>&1; then
  echo "check-changelog: comparison ref '$base' not found" >&2
  exit 2
fi

merge_base=$(git merge-base HEAD "$base") || {
  echo "check-changelog: failed to compute merge-base with '$base'" >&2
  exit 2
}

# Files changed between merge-base and HEAD.
changed_files=$(git diff --name-only "$merge_base"..HEAD)

if [ -z "$changed_files" ]; then
  echo "check-changelog: ok (no changes since merge-base with $base)"
  exit 0
fi

# Public-API surface, per binding.  Each entry is a grep -E pattern.
api_patterns=(
  '^python/aletheia/'
  '^go/aletheia/[^/]+\.go$'
  '^cpp/include/aletheia/'
  '^haskell-shim/ffi-exports\.snapshot$'
)

# Test exclusions.  These paths host test code, never public API.
test_exclusions='_test\.go$|/tests/|^python/aletheia/.*/test_|^cpp/tests/'

api_changed_files=""
for pattern in "${api_patterns[@]}"; do
  matched=$(echo "$changed_files" | grep -E "$pattern" | grep -v -E "$test_exclusions" || true)
  if [ -n "$matched" ]; then
    api_changed_files+="$matched"$'\n'
  fi
done

if [ -z "$api_changed_files" ]; then
  echo "check-changelog: ok (no public-API changes since merge-base with $base)"
  exit 0
fi

# Public API changed — require CHANGELOG.md to be in the diff.
if echo "$changed_files" | grep -qE '^CHANGELOG\.md$'; then
  echo "check-changelog: ok (public-API changes accompanied by CHANGELOG.md edit)"
  exit 0
fi

cat >&2 <<EOF
check-changelog: FAIL — public-API changes detected without a CHANGELOG.md entry.

Changed public-API files:
$(echo "$api_changed_files" | sed 's/^/  /' | grep -v '^  $')

Required: add an entry to CHANGELOG.md under '## [X.Y.Z] — Unreleased' before
merging.  Use one of:

  ### Added       — new public surface
  ### Changed     — modified existing surface (incl. BREAKING)
  ### Removed     — dropped surface
  ### Fixed       — behavior fix on existing surface

If the diff is an internal-only refactor (no observable surface change),
add a note under '### Changed' explaining "internal refactor — no behavior
change" so reviewers can verify by inspection.

Reference: R18 Universal Rule UR-1 (Public API stability and CHANGELOG discipline).
EOF
exit 1
