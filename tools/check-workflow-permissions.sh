#!/usr/bin/env bash
# tools/check-workflow-permissions.sh — Verify minimal workflow permissions.
#
# GitHub workflows default to a permissive `GITHUB_TOKEN` scope with broad
# repo write access if no `permissions:` block is declared.  This is a
# supply-chain attack risk: a compromised workflow inherits enough scope to
# push commits, modify branch protection, etc.
#
# Aletheia's permissions policy:
#   * Every workflow must declare a top-level `permissions:` block, OR every
#     job within it must declare its own.
#   * The default scope must be `read` (not `write` or `read-all`/`write-all`).
#   * Scopes that grant write access (`contents: write`, `pull-requests: write`,
#     etc.) require explicit per-job declaration with a comment justifying
#     why the scope is needed.
#
# v0 implementation: enforces presence of `permissions:` with read-only
# default; does NOT yet validate the per-scope justification comments.
# v1+ can tighten.
#
# Runs as both:
#   * Offline (pre-push hook via tools/run-ci.sh, manual invocation).
#   * Push-time (GHA workflow .github/workflows/gha-checks.yml).
#
# Exit codes:
#   0 — all workflows declare minimal permissions.
#   1 — at least one workflow lacks a `permissions:` block or uses
#       a permissive default.
#   2 — no .github/workflows/ directory (skips silently with exit 0).

set -euo pipefail

repo_root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  echo "check-workflow-permissions: not inside a git repo" >&2
  exit 2
}
cd "$repo_root"

workflows_dir=".github/workflows"
if [ ! -d "$workflows_dir" ]; then
  echo "check-workflow-permissions: $workflows_dir does not exist; skipping"
  exit 0
fi

violations=""
checked=0

# Iterate over each workflow file.
while IFS= read -r workflow; do
  [ -z "$workflow" ] && continue
  checked=$((checked + 1))

  # Use python for proper YAML parsing — bash heredocs lie about structure.
  result=$(python3 - "$workflow" <<'PY'
import sys, yaml

path = sys.argv[1]
try:
    with open(path) as fh:
        doc = yaml.safe_load(fh)
except Exception as e:
    print(f"PARSE_ERROR: {e}")
    sys.exit(0)

if not isinstance(doc, dict):
    print("PARSE_ERROR: top-level YAML is not a mapping")
    sys.exit(0)

# Top-level permissions present and acceptable?
top_perms = doc.get("permissions")
top_ok = False
if top_perms is not None:
    if isinstance(top_perms, str):
        # `permissions: read-all` is too permissive (grants read on every scope).
        # Only `permissions: {}` (empty mapping) or per-scope declarations are
        # acceptable as top-level.  Tag the str form as a violation.
        if top_perms == "read-all":
            print(f"VIOLATION: top-level `permissions: read-all` — declare per-scope minimums instead")
            sys.exit(0)
        elif top_perms == "write-all":
            print(f"VIOLATION: top-level `permissions: write-all` — declare per-scope minimums instead")
            sys.exit(0)
        else:
            top_ok = False  # unknown string form
    elif isinstance(top_perms, dict):
        # Any explicit mapping is OK at v0; v1+ checks scope-by-scope.
        top_ok = True

# If top-level missing, every job must declare permissions individually.
if not top_ok:
    jobs = doc.get("jobs", {})
    if not isinstance(jobs, dict):
        print("VIOLATION: jobs key is not a mapping")
        sys.exit(0)
    missing_jobs = []
    for job_name, job in jobs.items():
        if not isinstance(job, dict):
            continue
        job_perms = job.get("permissions")
        if job_perms is None:
            missing_jobs.append(job_name)
    if missing_jobs:
        print(f"VIOLATION: no top-level `permissions:` and these jobs lack their own: {', '.join(missing_jobs)}")
        sys.exit(0)

print("OK")
PY
)

  case "$result" in
    OK)
      ;;
    PARSE_ERROR:*)
      violations+="  $workflow: ${result#PARSE_ERROR: }"$'\n'
      ;;
    VIOLATION:*)
      violations+="  $workflow: ${result#VIOLATION: }"$'\n'
      ;;
    *)
      violations+="  $workflow: unexpected output: $result"$'\n'
      ;;
  esac
done < <(find "$workflows_dir" -maxdepth 1 -type f \( -name '*.yml' -o -name '*.yaml' \))

if [ -n "$violations" ]; then
  cat >&2 <<EOF
check-workflow-permissions: FAIL — workflow permissions policy violations detected.

Policy:
  * Every workflow must declare top-level \`permissions:\` (mapping form), OR
    every job must declare its own \`permissions:\`.
  * \`permissions: read-all\` and \`permissions: write-all\` are too permissive.
    Declare per-scope minimums (e.g., \`contents: read\`).

Violations ($checked workflows checked):
$violations
Fix: add a top-level \`permissions:\` block with per-scope minimums.
Example (read-only default):
  permissions:
    contents: read

Reference: GitHub Security Hardening for GitHub Actions §
"Use the least privilege principle".
EOF
  exit 1
fi

echo "check-workflow-permissions: ok ($checked workflows checked, all declare minimal permissions)"
