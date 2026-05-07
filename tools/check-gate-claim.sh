#!/usr/bin/env bash
# tools/check-gate-claim.sh — Enforce gate-claim integrity (R18 cluster 1 phase 2).
#
# Mechanical enforcer for `memory/feedback_gate_claim_integrity.md`.  When a
# commit message contains a gate-clean assertion ("all gates clean", "gates
# green", etc.), verify that `build/libaletheia-ffi.so` mtime postdates every
# build-relevant staged source file's mtime — i.e., the gates the commit
# claims to have run on actually observed the post-edit state.
#
# Usage:
#   tools/check-gate-claim.sh                # pre-commit mode (read .git/COMMIT_EDITMSG)
#   tools/check-gate-claim.sh HEAD           # post-commit mode (read HEAD's message)
#   tools/check-gate-claim.sh <commit-hash>  # audit mode (read named commit's message)
#
# Strategy:
# 1. Identify commit message + diffed files (mode-dependent).
# 2. Pattern-match the message for gate-claim phrases.  If no claim, exit 0.
# 3. Filter diff to build-relevant paths (Agda src, Shakefile, haskell-shim, etc.).
# 4. If filter is empty, exit 0 (doc-only or binding-only edits don't invalidate the .so).
# 5. Compare each build-relevant file's mtime against build/libaletheia-ffi.so mtime.
#    Any file newer than the .so → fail with diagnostic.
#
# Exit codes:
#   0 — no claim, OR claim with stale-file-free state.
#   1 — claim made but .so missing or stale relative to build-relevant edits.
#   2 — usage error / git failure.
#
# v0 limitations (deliberate; documented for the v1+ artifact-based design):
#   * mtime-based, not artifact-based.  A v1+ design will require an attached
#     `tools/ci-output/<sha>.log` artifact emitted by Phase 3's Shake `phony
#     "ci"` orchestrator, with content asserting the full gate sweep
#     succeeded.  v0 stops at the .so freshness invariant.
#   * Edge case: post-`git checkout` mtime resets all files to checkout time.
#     The check therefore noisily fails right after a fresh clone or branch
#     switch.  Acceptable v0: the enforcer is only load-bearing at commit
#     time on the dev's actual working state, where mtime tracks edits
#     correctly.
#   * Claim phrases are conservative.  Specific gate-output lines like
#     "check-properties ✓" don't match; only broader "all gates" / "gates
#     green" / "All N gates" assertions trigger the freshness check.

set -euo pipefail

mode="${1:-pre-commit}"

# ─── Step 1: identify commit message + diffed files ──────────────────────────

case "$mode" in
  pre-commit)
    msg_file=".git/COMMIT_EDITMSG"
    if [ ! -f "$msg_file" ]; then
      # Pre-commit hook not active or no edit msg in flight; nothing to enforce.
      exit 0
    fi
    msg=$(cat "$msg_file")
    diff_files=$(git diff --name-only --cached)
    ;;
  HEAD|post-commit)
    msg=$(git log -1 --format=%B HEAD)
    diff_files=$(git diff-tree --no-commit-id --name-only -r HEAD)
    ;;
  *)
    # Treat as a commit hash / ref
    if ! git rev-parse --verify "$mode" >/dev/null 2>&1; then
      echo "check-gate-claim: usage: $0 [pre-commit|HEAD|<commit-hash>]" >&2
      exit 2
    fi
    msg=$(git log -1 --format=%B "$mode")
    diff_files=$(git diff-tree --no-commit-id --name-only -r "$mode")
    ;;
esac

# ─── Step 2: pattern-match for gate-claim phrases ────────────────────────────

# Conservative pattern: only triggers on broad "all gates" / "gates green" /
# "All N gates" assertions, not on per-gate status lines.
gate_claim_pattern='([Aa]ll [0-9]* ?[Aa]gda gates (clean|green|passed))|([Aa]ll gates (clean|green|passed))|([Gg]ates? (green|clean)\b)|(All proof modules type-checked successfully)'

if ! echo "$msg" | grep -qE "$gate_claim_pattern"; then
  # No gate-claim assertion; freshness check not applicable.
  exit 0
fi

# ─── Step 3: filter diff to build-relevant paths ─────────────────────────────

# These are the paths that, when modified, can invalidate the .so build.
# Doc / binding-test / lint-config edits are NOT build-relevant.
build_relevant_pattern='(^src/.*\.agda$)|(^Shakefile\.hs$)|(^haskell-shim/.*\.(hs|cabal)$)|(^aletheia\.agda-lib$)'

build_relevant_files=$(echo "$diff_files" | grep -E "$build_relevant_pattern" || true)

if [ -z "$build_relevant_files" ]; then
  # Doc-only / binding-only / lint-config-only commit; .so freshness immaterial.
  exit 0
fi

# ─── Step 4: verify .so freshness ────────────────────────────────────────────

so_path="build/libaletheia-ffi.so"
if [ ! -f "$so_path" ]; then
  cat >&2 <<EOF
check-gate-claim: FAIL — commit claims gates clean but $so_path does not exist.

The gate runs in the commit message must have produced the .so artifact.
Run \`cabal run shake -- build\` to produce it, then re-run the gates
the message asserts.

Reference: memory/feedback_gate_claim_integrity.md
EOF
  exit 1
fi

so_mtime=$(stat -c %Y "$so_path")
stale_files=""
while IFS= read -r f; do
  [ -z "$f" ] && continue
  if [ -f "$f" ]; then
    f_mtime=$(stat -c %Y "$f")
    if [ "$f_mtime" -gt "$so_mtime" ]; then
      stale_files+="  $f (mtime $(date -d "@$f_mtime" "+%Y-%m-%d %H:%M:%S"))"$'\n'
    fi
  fi
done <<< "$build_relevant_files"

if [ -n "$stale_files" ]; then
  cat >&2 <<EOF
check-gate-claim: FAIL — gate-clean claim made without fresh build artifact.

build/libaletheia-ffi.so mtime: $(date -d "@$so_mtime" "+%Y-%m-%d %H:%M:%S")

Build-relevant source files NEWER than the .so:
$stale_files
The gate runs the commit message asserts must have observed these source
files.  Re-run the affected gates BEFORE committing the claim:

  cabal run shake -- build
  cabal run shake -- check-properties
  cabal run shake -- check-invariants
  cabal run shake -- check-no-properties-in-runtime
  cabal run shake -- check-erasure
  cabal run shake -- check-fidelity
  cabal run shake -- check-ffi-exports
  cabal run shake -- count-modules

Reference: memory/feedback_gate_claim_integrity.md
EOF
  exit 1
fi

echo "check-gate-claim: ok (.so mtime postdates all build-relevant staged files)"
