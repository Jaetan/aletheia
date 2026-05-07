#!/usr/bin/env bash
# tools/run-ci.sh — Offline CI orchestrator (R18 cluster 1 phase 3).
#
# Chains the full gate sweep that commit messages have historically asserted
# "all gates clean / green" against, plus the cluster 1 phase 1+2 enforcers
# (check-changelog, check-gate-claim).  Captures all output to a timestamped
# log under `tools/ci-output/` so the gate-claim-integrity enforcer can
# point at it as falsifiable evidence (v1+ artifact-based design).
#
# Invoked from:
#   * `tools/run-ci.sh` (direct, manual or scripted)
#   * `.git/hooks/pre-push` (auto-installed by tools/install-hooks.sh)
#
# Deliberately NOT exposed as a Shake `phony "ci"` target — the runner's
# inner `cabal run shake -- build` invocation fails to acquire cabal-install's
# `dist-newstyle/` flock when the parent process is itself `cabal run`.
# Direct invocation avoids the flock-recursion entirely.  See Shakefile.hs
# comment block where the `ci` phony would otherwise live.
#
# Sequence (sequential — fast-fail on any non-zero exit):
#   Agda gates (8):
#      1. build           — produces libaletheia-ffi.so
#      2. check-properties     (longest, ~8-10 min)
#      3. check-invariants
#      4. check-no-properties-in-runtime
#      5. check-erasure
#      6. check-fidelity       (~2 min — runs ConstructorTest binary)
#      7. check-ffi-exports
#      8. count-modules
#   Offline enforcers (2):
#      9. check-changelog
#     10. check-gate-claim
#   Binding tests (3):
#     11. Python pytest
#     12. Go test -race
#     13. C++ ctest
#   Lints (4):
#     14. basedpyright (Python)
#     15. pylint 10/10 (Python)
#     16. gofmt -d + go vet (Go)
#     17. clang-format --dry-run --Werror (C++)
#
# Total ~12-15 min on a warm system.
#
# Benchmarks are NOT included — performance regression detection is a
# separate concern from correctness, and run_all.sh is invoked manually
# when changes touch the streaming hot path (see CLAUDE.md § Performance
# Considerations + AGENTS.md § Step 4).
#
# Exit codes:
#   0 — all 17 steps passed.
#   1 — at least one step failed; tail of log printed to stderr.
#   2 — usage error (e.g., not in a git repo, missing dependency).

set -euo pipefail

# ─── Setup ────────────────────────────────────────────────────────────────────

repo_root=$(git rev-parse --show-toplevel 2>/dev/null) || {
  echo "run-ci: not inside a git repo" >&2
  exit 2
}
cd "$repo_root"

log_dir="tools/ci-output"
mkdir -p "$log_dir"

branch=$(git rev-parse --abbrev-ref HEAD)
# Sanitize branch name for filesystem
branch_safe=$(echo "$branch" | tr -c '[:alnum:]_.-' '_')
timestamp=$(date -u +%Y-%m-%dT%H-%M-%SZ)
log_file="$log_dir/ci-$branch_safe-$timestamp.log"

ci_start=$(date +%s)

# ─── Header ───────────────────────────────────────────────────────────────────

{
  echo "═══ Aletheia offline CI sweep ═══"
  echo "Started:  $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "Branch:   $branch"
  echo "Commit:   $(git rev-parse HEAD)"
  echo "Tree:     $(git log -1 --format=%H HEAD)"
  echo "Log:      $log_file"
  echo
} | tee "$log_file"

# ─── Step framework ───────────────────────────────────────────────────────────

step_num=0
total_steps=17
failed_step=""

run_step() {
  local name="$1"
  shift
  step_num=$((step_num + 1))
  local step_start=$(date +%s)
  {
    echo
    echo "─── Step $step_num/$total_steps: $name ───"
    echo "Cmd:    $*"
    echo "Start:  $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  } | tee -a "$log_file"
  if "$@" >>"$log_file" 2>&1; then
    local step_end=$(date +%s)
    local duration=$((step_end - step_start))
    echo "  ✓ $name (${duration}s)" | tee -a "$log_file" >&2
  else
    local exit_code=$?
    local step_end=$(date +%s)
    local duration=$((step_end - step_start))
    failed_step="$name"
    {
      echo "  ✗ $name FAILED (exit $exit_code, ${duration}s)"
      echo
      echo "─── Tail of failed step output ───"
    } | tee -a "$log_file" >&2
    tail -50 "$log_file" >&2
    {
      echo
      echo "═══ CI FAILED at step $step_num/$total_steps: $name ═══"
      echo "Full log: $log_file"
    } | tee -a "$log_file" >&2
    return 1
  fi
}

# Wrapper for cd-then-run binding-test commands.
run_step_in() {
  local subdir="$1"
  local name="$2"
  shift 2
  run_step "$name" bash -c "cd '$subdir' && $*"
}

# ─── Steps 1-8: Agda gates ───────────────────────────────────────────────────

run_step "build" cabal run shake -- build
run_step "check-properties" cabal run shake -- check-properties
run_step "check-invariants" cabal run shake -- check-invariants
run_step "check-no-properties-in-runtime" cabal run shake -- check-no-properties-in-runtime
run_step "check-erasure" cabal run shake -- check-erasure
run_step "check-fidelity" cabal run shake -- check-fidelity
run_step "check-ffi-exports" cabal run shake -- check-ffi-exports
run_step "count-modules" cabal run shake -- count-modules

# ─── Steps 9-10: Offline enforcers ───────────────────────────────────────────

run_step "check-changelog" cabal run shake -- check-changelog
run_step "check-gate-claim" cabal run shake -- check-gate-claim

# ─── Steps 11-13: Binding tests ──────────────────────────────────────────────

run_step_in "python" "pytest" python3 -m pytest tests/
run_step_in "go" "go test -race" go test ./aletheia/ -count=1 -race
run_step_in "cpp" "ctest" bash -c "cmake -B build >/dev/null && cmake --build build && ctest --test-dir build"

# ─── Steps 14-17: Lints ──────────────────────────────────────────────────────

run_step_in "python" "basedpyright" basedpyright aletheia/
run_step_in "python" "pylint" pylint aletheia/ tests/
run_step_in "go" "gofmt + go vet" bash -c "gofmt -d ./aletheia/ && go vet ./aletheia/"
run_step_in "cpp" "clang-format" bash -c "find . -name '*.cpp' -o -name '*.hpp' | xargs clang-format --dry-run --Werror"

# ─── Final summary ────────────────────────────────────────────────────────────

ci_end=$(date +%s)
total_duration=$((ci_end - ci_start))

{
  echo
  echo "═══ CI summary ═══"
  echo "Result:   ALL $total_steps STEPS PASSED"
  echo "Duration: ${total_duration}s ($(printf '%dm%02ds' $((total_duration / 60)) $((total_duration % 60))))"
  echo "Log:      $log_file"
  echo "Use this log file as the falsifiable evidence behind any 'all gates'"
  echo "claim in commit messages (see memory/feedback_gate_claim_integrity.md)."
} | tee -a "$log_file"
