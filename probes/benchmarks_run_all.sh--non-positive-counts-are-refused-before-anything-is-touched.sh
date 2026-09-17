#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh.
# Claim: --frames and --runs accept only a positive integer and --warmup only
# a non-negative one, and a refused value is rejected before the mode check,
# every preflight and the results clear, so a file matching the mode's glob
# survives the refusal; a valid count reaches the mode check. Zero is
# meaningful for the warmup alone, where it says measure from cold, so it is
# checked as accepted rather than refused.
# Non-zero exit: a bad count was accepted, the refusal cleared a result, or a
# good count was refused.
set -u
cd "$(dirname "$0")/.." || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
sentinel="$dir/sentinel_throughput.json"
status=0
for bad in 0 -1 abc 1.5 ""; do
    for opt in --frames --runs; do
        echo '{}' > "$sentinel"
        out=$(ALETHEIA_BENCH_RESULTS_DIR="$dir" bash benchmarks/run_all.sh \
            $opt "$bad" --bench throughput 2>&1)
        rc=$?
        if [ "$rc" -eq 0 ] || ! grep -q -- "$opt must be a positive integer" <<< "$out"; then
            echo "accepted $opt '$bad' (exit $rc)"; status=1
        fi
        [ -f "$sentinel" ] || { echo "refusing $opt '$bad' cleared a result"; status=1; }
    done
done
# The warmup takes a non-negative integer: zero is a real choice there.
for bad in -1 abc 1.5 ""; do
    echo '{}' > "$sentinel"
    out=$(ALETHEIA_BENCH_RESULTS_DIR="$dir" bash benchmarks/run_all.sh \
        --warmup "$bad" --bench throughput 2>&1)
    rc=$?
    if [ "$rc" -eq 0 ] || ! grep -q -- "--warmup must be a non-negative integer" <<< "$out"; then
        echo "accepted --warmup '$bad' (exit $rc)"; status=1
    fi
    [ -f "$sentinel" ] || { echo "refusing --warmup '$bad' cleared a result"; status=1; }
done
out=$(ALETHEIA_BENCH_RESULTS_DIR="$dir" bash benchmarks/run_all.sh \
    --warmup 0 --bench bogus 2>&1)
grep -q -- "--warmup must be" <<< "$out" && { echo "a warmup of zero was refused"; status=1; }

# A valid pair passes the count check: the next check, the mode, is what refuses.
out=$(ALETHEIA_BENCH_RESULTS_DIR="$dir" bash benchmarks/run_all.sh \
    --frames 10000 --runs 5 --bench bogus 2>&1)
grep -q "unknown --bench" <<< "$out" || { echo "a valid count did not reach the mode check"; status=1; }
grep -q "positive integer" <<< "$out" && { echo "a valid count was refused"; status=1; }
exit $status
