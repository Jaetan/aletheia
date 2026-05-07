#!/usr/bin/env bash
# tools/install-hooks.sh — Install Aletheia's offline-CI git hooks.
#
# Idempotent: safe to re-run.  Skips installation if the existing hook
# already invokes our runner (detected by the marker comment line).
#
# Hooks installed:
#   * pre-push — runs `tools/run-ci.sh` before allowing push.
#                Refuses push on any non-zero exit.  Rationale: limited
#                GitHub Actions monthly allotment; offline validation
#                catches breakage before it lands on origin.
#
# Skip via:
#   git push --no-verify
#
# Reference: R18 cluster 1 phase 3 / memory/feedback_gate_claim_integrity.md.

set -euo pipefail

repo_root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  echo "install-hooks: not inside a git repo" >&2
  exit 2
}
cd "$repo_root"

hooks_dir=$(git rev-parse --git-path hooks)
mkdir -p "$hooks_dir"

marker="# aletheia-pre-push-marker (R18 cluster 1 phase 3)"

pre_push="$hooks_dir/pre-push"

if [ -f "$pre_push" ] && grep -qF "$marker" "$pre_push"; then
  echo "install-hooks: pre-push hook already installed (marker found at $pre_push)"
  exit 0
fi

if [ -f "$pre_push" ]; then
  backup="$pre_push.aletheia-backup-$(date +%s)"
  echo "install-hooks: existing pre-push hook backed up to $backup" >&2
  cp "$pre_push" "$backup"
fi

cat > "$pre_push" <<'HOOK'
#!/usr/bin/env bash
# aletheia-pre-push-marker (R18 cluster 1 phase 3)
#
# Pre-push hook installed by tools/install-hooks.sh.  Runs the full offline
# CI sweep before allowing push.  Skip with `git push --no-verify`.
#
# The pre-push hook receives <remote> <url> on argv and a list of
# refs being pushed on stdin.  We don't filter by ref — every push runs
# the full sweep — because the gate-claim-integrity rule requires
# evidence for the tip commit being pushed.

set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
runner="$repo_root/tools/run-ci.sh"

if [ ! -x "$runner" ]; then
  echo "pre-push: $runner not found or not executable; skipping" >&2
  exit 0
fi

echo "pre-push: running offline CI sweep (~12-15 min)..." >&2
echo "pre-push: skip with \`git push --no-verify\` if needed" >&2
echo >&2

if ! "$runner"; then
  echo >&2
  echo "pre-push: CI sweep failed — push refused." >&2
  echo "pre-push: review the log under tools/ci-output/, fix issues, re-push." >&2
  echo "pre-push: bypass with \`git push --no-verify\` only when you understand why." >&2
  exit 1
fi

echo "pre-push: CI sweep passed — push allowed." >&2
exit 0
HOOK

chmod +x "$pre_push"
echo "install-hooks: pre-push hook installed at $pre_push"
echo "install-hooks: every \`git push\` will now run \`tools/run-ci.sh\` first"
echo "install-hooks: bypass with \`git push --no-verify\`"
