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
#   Lints (5):
#     14. basedpyright (Python)
#     15. pylint 10/10 (Python — SCORE-based gate per AGENTS.md L611)
#     16. gofmt -l + go vet (Go)
#     17. clang-format --dry-run --Werror (C++)
#     18. clang-tidy -p build (C++ — mandatory per AGENTS.md L494)
#   GHA meta-checks (3):
#     19. actionlint (workflow YAML lint, skipped if not installed)
#     20. check-action-pins.sh
#     21. check-workflow-permissions.sh
#
# Total ~15-20 min on a warm system (clang-tidy adds ~3-5 min on top of the
# previous 12-15 min baseline).
#
# Benchmarks are NOT included — performance regression detection is a
# separate concern from correctness, and run_all.sh is invoked manually
# when changes touch the streaming hot path (see CLAUDE.md § Performance
# Considerations + AGENTS.md § Step 4).
#
# Exit codes:
#   0 — all 21 steps passed (or skipped where allowed).
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
total_steps=21
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
# IMPORTANT — direct run_step (not run_step_in) for any inner pipeline / multi-
# command bash invocation: run_step_in collapses its remaining args via $* with
# loss of quoting, so an inner `bash -c "..."` ends up as `bash -c <first-word>
# arg1 arg2 ...`.  The inner bash then runs only the first word as the command;
# remaining tokens become positional args, the pipe/redirect/&& happen in the
# OUTER shell, and silent no-ops slip through.  All the multi-command lint /
# binding-test steps below use direct run_step + a single bash -c with cd
# folded in.
run_step "ctest" bash -c "cd cpp && cmake -B build > /dev/null && cmake --build build && ctest --test-dir build"

# ─── Steps 14-18: Lints ──────────────────────────────────────────────────────

run_step_in "python" "basedpyright" basedpyright aletheia/
# pylint: gate is SCORE-based per AGENTS.md L611 ("pylint score must stay
# 10.00/10") and feedback_pylint_10_mandatory.md.  Pylint's exit code is a
# bit-flag (1=fatal/2=error/4=warning/8=refactor/16=convention) — exit 8 fires
# even when the score is 10/10 (refactor messages like R0801 duplicate-code do
# not deduct from the score formula).  Score check matches the established
# policy; exit-code check would be stricter than the project requires.
run_step "pylint" bash -c "cd python && pylint aletheia/ tests/ > /tmp/aletheia-pylint.out 2>&1; cat /tmp/aletheia-pylint.out; grep -q 'rated at 10\\.00/10' /tmp/aletheia-pylint.out"
# gofmt -l (LIST) — exits 0 normally but emits filenames needing reformatting
# on stdout; gate fails iff output non-empty OR gofmt returned non-zero (e.g.
# Go syntax error).  Old `-d` (DIFF) printed the diff but exited 0 even on
# dirty source, so wasn't a real gate (matches AGENTS.md L190 which uses -l).
# Capture rc separately from output to avoid the `$(...)`-masks-rc trap.
run_step "gofmt + go vet" bash -c 'cd go && gofmt -l ./aletheia/ > /tmp/aletheia-gofmt.out 2>&1; rc=$?; cat /tmp/aletheia-gofmt.out; test $rc -eq 0 && test ! -s /tmp/aletheia-gofmt.out && go vet ./aletheia/'
# clang-format: exclude build/, build-tidy/, _deps/ which contain generated /
# third-party code that the project does NOT format.
run_step "clang-format" bash -c "cd cpp && find . \\( -path ./build -o -path ./build-tidy -o -path ./_deps -o -path './*/_deps' \\) -prune -o \\( -name '*.cpp' -o -name '*.hpp' \\) -print | xargs clang-format --dry-run --Werror"
# clang-tidy: mandatory per AGENTS.md L494 ("zero errors and zero warnings on
# all source files") + feedback_clang_tidy_mandatory.md.  Reads
# compile_commands.json from build/ (CMake exports by default).  Canonical
# invocation per AGENTS.md L580 — src/*.cpp only (the "source files" the rule
# scopes; tests/*.cpp are not in the canonical scope).  Faster than
# -DALETHEIA_CLANG_TIDY=ON rebuild.
run_step "clang-tidy" bash -c "cd cpp && clang-tidy -p build src/*.cpp"

# ─── Steps 19-21: GHA meta-checks ────────────────────────────────────────────

# actionlint is optional locally — workflow gates against it server-side.
# If not installed, skip with a warning rather than fail.
if command -v actionlint >/dev/null 2>&1; then
  if [ -d .github/workflows ]; then
    run_step "actionlint" actionlint -color
  else
    step_num=$((step_num + 1))
    echo "  ⊘ actionlint skipped (no .github/workflows/ directory)" | tee -a "$log_file" >&2
  fi
else
  step_num=$((step_num + 1))
  echo "  ⊘ actionlint skipped (binary not installed; see docs/development/CI_LOCAL.md)" | tee -a "$log_file" >&2
fi

run_step "check-action-pins" tools/check-action-pins.sh
run_step "check-workflow-permissions" tools/check-workflow-permissions.sh

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
