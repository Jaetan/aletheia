#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh.
# Claim: --warmup is the latency mode's, and a value given for another mode is
# refused rather than accepted and dropped. The unit differs by mode: latency
# warms in operations, throughput in whole runs of the frame set, so the one
# number the runner holds cannot serve both and only the latency arms pass it.
# The refusal lands before the results clear, so a file matching the mode's glob
# survives it. The latency mode itself still takes the flag, and the banner
# names the warmup it was given rather than a count that mode never reads.
# Non-zero exit: a warmup for another mode was accepted, the refusal cleared a
# result, or the latency mode stopped taking the flag.
set -u
cd "$(dirname "$0")/.." || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
status=0

for mode in throughput scaling; do
    sentinel="$dir/sentinel_${mode}.json"
    echo '{}' > "$sentinel"
    out=$(ALETHEIA_BENCH_RESULTS_DIR="$dir" bash benchmarks/run_all.sh \
        --bench "$mode" --warmup 7 2>&1)
    rc=$?
    if [ "$rc" -eq 0 ] || ! grep -q -- "--warmup is the latency mode's" <<< "$out"; then
        echo "the $mode mode accepted a warmup it cannot use (exit $rc)"; status=1
    fi
    [ -f "$sentinel" ] || { echo "refusing a warmup for $mode cleared a result"; status=1; }
done

# The latency mode takes it, and says so: one operation a lane is enough to
# reach the banner and the lanes, the binaries being built incrementally.
out=$(ALETHEIA_BENCH_RESULTS_DIR="$dir" bash benchmarks/run_all.sh \
    --bench latency --frames 1 --warmup 7 2>&1)
rc=$?
if [ "$rc" -ne 0 ]; then
    echo "the latency mode refused a warmup (exit $rc)"
    echo "$out" | tail -5
    status=1
fi
grep -qE "^Warmup: +7$" <<< "$out" || { echo "the latency run did not report the warmup it was given"; status=1; }
grep -qE "^Runs:" <<< "$out" && { echo "the latency run reported a run count it never reads"; status=1; }
exit $status
