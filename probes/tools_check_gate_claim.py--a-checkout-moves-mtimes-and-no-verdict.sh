#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/check_gate_claim.py.
# Claim: a gate-clean claim is judged by whether a sweep recorded the
# commit's build sources, and by nothing a checkout can move. In a throwaway
# repository whose one commit claims the gates clean over an Agda module, the
# check passes when a passed sweep log records the commit's digest, with every
# source dated an hour past every other file and no shared library on disk at
# all; it fails, naming the digest and the sweep as the remedy, once that log
# is gone; and a log that recorded no digest, the shape a fast-tier sweep
# leaves, is not the record either.
# Non-zero exit: the check reads a timestamp, accepts a claim no sweep
# recorded, or accepts a fast-tier log as evidence. Exits 2 when git or the
# interpreter is missing.
set -u
cd "$(dirname "$0")/.." || exit 2
repo=$PWD
py=$repo/python/.venv/bin/python
command -v git > /dev/null && [ -x "$py" ] || exit 2
scratch=cpp/build/probe-scratch/gate-claim
rm -rf "$scratch"
mkdir -p "$scratch/src" || exit 2
# The check finds its repository through git from the working directory, and
# the copy of the package is what puts the throwaway repository in scope.
cp -r tools "$scratch/tools" || exit 2
rm -rf "$scratch/tools/ci-output"
(
    cd "$scratch" || exit 2
    git init -q -b main .
    printf 'module A where\n' > src/A.agda
    git add -A
    git -c user.email=probe@example.com -c user.name=probe -c commit.gpgsign=false \
        commit -q -m 'feat: a module' -m 'All gates clean.'
) || exit 2

run() { (cd "$scratch" && env -u ALETHEIA_GATE_SOURCES "$py" -m tools.check_gate_claim HEAD 2>&1); }
digest=$(cd "$scratch" && "$py" -c 'from tools.check_gate_claim import sources_digest_of_revision as d; print(d("HEAD"))') || exit 2
case $digest in ????????????????????????????????????????????????????????????????) ;; *) echo "no digest: $digest"; exit 2 ;; esac

log_dir=$scratch/tools/ci-output
mkdir -p "$log_dir"
write_log() {
    printf '═══ Aletheia offline CI sweep ═══\nBranch:   main\nSources:  %s\nSteps:    3\n─── build (0s) ───\n  ✓ build (0s)\n═══ CI summary ═══\nResult:   ALL 3 STEPS PASSED\nDuration: 1s (0m01s)\n' "$2" > "$log_dir/$1"
}
write_log ci-main.log "$digest"
# Every source an hour past the log and past anything else on disk: the
# reading the retired comparison took as staleness.
touch -d '+1 hour' "$scratch/src/A.agda"

out=$(run); rc=$?
[ "$rc" -eq 0 ] || { echo "a recorded claim was refused over moved mtimes: $out"; exit 1; }
case $out in *"passed sweep"*) ;; *) echo "the pass does not cite the log: $out"; exit 1 ;; esac

rm -f "$log_dir/ci-main.log"
out=$(run); rc=$?
[ "$rc" -eq 1 ] || { echo "an unrecorded claim was accepted (exit $rc): $out"; exit 1; }
case $out in *"$digest"*) ;; *) echo "the refusal does not name the digest: $out"; exit 1 ;; esac
case $out in *"tools/run_ci.py"*) ;; *) echo "the refusal does not name the sweep as the remedy: $out"; exit 1 ;; esac

write_log ci-fast.log "none (a fast-tier sweep runs a subset)"
out=$(run); rc=$?
[ "$rc" -eq 1 ] || { echo "a fast-tier log was accepted as evidence (exit $rc): $out"; exit 1; }
rm -rf "$scratch"
