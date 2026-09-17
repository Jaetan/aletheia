#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh.
# Claim: every flag the selected mode does not read is refused, and every flag
# it does read still reaches it. The throughput mode reads both counts, the
# latency mode reads the frame count as its operation count and the warmup, and
# the scaling mode picks its own trace sizes and reads the run count alone.
# A flag outside its mode's set used to be accepted and dropped, so a run
# measured the default while reporting the number the caller asked for.
# The refusal lands before the results are cleared, so a file matching the
# mode's glob survives it, and before the results directory is made, which is
# what the accepted cases here check: given only what its mode reads, each mode
# gets as far as creating that directory and fails on the directory alone.
# The latency mode's banner is checked too, for naming the warmup it was given
# and not a run count it never reads.
# Non-zero exit: a flag outside the mode's set was accepted, the refusal
# cleared a result, or a flag the mode reads was refused.
set -u
cd "$(dirname "$0")/.." || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
status=0

refused() { # mode flag value
	local mode=$1 flag=$2 value=$3 sentinel="$dir/sentinel_$1.json" out rc
	echo '{}' > "$sentinel"
	out=$(ALETHEIA_BENCH_RESULTS_DIR="$dir" bash benchmarks/run_all.sh \
		--bench "$mode" "$flag" "$value" 2>&1)
	rc=$?
	if [ "$rc" -eq 0 ] || ! grep -q -- "$flag is not read by the $mode mode" <<< "$out"; then
		echo "the $mode mode accepted $flag, which it does not read (exit $rc)"
		status=1
	fi
	[ -f "$sentinel" ] || { echo "refusing $flag for $mode cleared a result"; status=1; }
}

refused latency --runs 3
refused scaling --frames 100
refused scaling --warmup 7
refused throughput --warmup 7

accepted() { # mode, then the flags that mode reads
	local mode=$1 out
	shift
	# An unwritable results directory aborts the run immediately after the
	# argument checks and before any lane, so this reaches the whole of the
	# checking without paying for a measurement.
	out=$(ALETHEIA_BENCH_RESULTS_DIR=/proc/no-such-directory/results \
		bash benchmarks/run_all.sh --bench "$mode" "$@" 2>&1)
	if grep -q "is not read by the $mode mode" <<< "$out"; then
		echo "the $mode mode refused a flag it reads: $*"
		echo "$out" | sed 's/^/    /'
		status=1
	fi
	grep -q "mkdir" <<< "$out" || {
		echo "the $mode mode did not reach the results directory with $*"
		echo "$out" | tail -3 | sed 's/^/    /'
		status=1
	}
}

accepted throughput --frames 10000 --runs 10
accepted latency --frames 10000 --warmup 500
accepted scaling --runs 10

# The latency mode runs and reports the warmup it was given. One operation a
# lane is enough to reach the banner and the lanes, the binaries being built
# incrementally.
out=$(ALETHEIA_BENCH_RESULTS_DIR="$dir" bash benchmarks/run_all.sh \
	--bench latency --frames 1 --warmup 7 2>&1)
rc=$?
if [ "$rc" -ne 0 ]; then
	echo "the latency mode refused what it reads (exit $rc)"
	echo "$out" | tail -5
	status=1
fi
grep -qE "^Warmup: +7$" <<< "$out" || { echo "the latency run did not report the warmup it was given"; status=1; }
grep -qE "^Runs:" <<< "$out" && { echo "the latency run reported a run count it never reads"; status=1; }
exit $status
