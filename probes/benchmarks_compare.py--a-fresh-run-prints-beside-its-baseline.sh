#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/compare.py.
# Claim: given one binding's fresh result file and its committed baseline for
# one mode, the comparison prints both as their own columns and, per lane, the
# current mean, the baseline mean, the delta between them and the current
# standard deviation, which is the shape AGENTS.md asks a benchmark report to
# carry. The two files share a language, and the script used to key its
# columns on the language alone, so the second file replaced the first without
# a word and a fresh run could not be read against its baseline at all.
# Non-zero exit: one of the two files is missing from the output, or the delta
# printed is not the one the two files give.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
base=benchmarks/results/cpp_throughput_baseline.json
cp "$base" "$dir/cpp_throughput_baseline.json" || exit 2
# The fresh file is the baseline with every mean scaled by one tenth up, so the
# delta every lane must print is known before the script runs.
"$py" - "$base" "$dir/cpp_throughput.json" <<'PY' || exit 2
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
for r in d["results"]:
    r["fps_mean"] = round(r["fps_mean"] * 1.1, 1)
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"))
PY
out=$("$py" benchmarks/compare.py "$dir/cpp_throughput.json" "$dir/cpp_throughput_baseline.json" 2>&1)
rc=$?
status=0
[ "$rc" -eq 0 ] || { echo "compare.py exited $rc"; echo "$out" | tail -5; status=1; }
grep -qE '(^| )cpp( |$)' <<< "$out" || { echo "no column for the fresh file"; status=1; }
grep -q 'cpp baseline' <<< "$out" || { echo "no column for the baseline file"; status=1; }
grep -qiE 'delta' <<< "$out" || { echo "no delta printed"; status=1; }
# Every lane of the delta table reads +10.0%, the change the fresh file was given.
lanes=$(grep -cE '\+10\.0%' <<< "$out")
want=$("$py" -c "import json; print(len(json.load(open('$base'))['results']))")
[ "$lanes" -eq "$want" ] || { echo "$lanes lanes print the +10.0% delta, the file has $want lanes"; echo "$out"; status=1; }
grep -qiE 'stdev|std' <<< "$out" || { echo "no standard deviation column"; status=1; }
exit $status
