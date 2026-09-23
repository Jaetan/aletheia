#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/compare.py.
# Claim: two result files that would print as the same column of the same
# table are refused, with both paths named, rather than the later one
# replacing the earlier without a word. A column is a binding and a mode, plus
# what the file's name adds beyond them, so two copies of one baseline from
# two directories are the collision this checks.
# Non-zero exit: the second file replaced the first and the script exited
# zero, or the refusal did not name both files.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
mkdir -p "$dir/a" "$dir/b" || exit 2
cp benchmarks/results/cpp_throughput_baseline.json "$dir/a/" || exit 2
cp benchmarks/results/cpp_throughput_baseline.json "$dir/b/" || exit 2
out=$("$py" benchmarks/compare.py "$dir/a/cpp_throughput_baseline.json" "$dir/b/cpp_throughput_baseline.json" 2>&1)
rc=$?
status=0
[ "$rc" -ne 0 ] || { echo "two files for one column were accepted (exit 0)"; status=1; }
grep -q "$dir/a/cpp_throughput_baseline.json" <<< "$out" || { echo "the refusal does not name the first file"; status=1; }
grep -q "$dir/b/cpp_throughput_baseline.json" <<< "$out" || { echo "the refusal does not name the second file"; status=1; }
[ "$status" -eq 0 ] || echo "$out" | tail -5
exit $status
