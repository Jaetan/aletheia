#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/benchmarks/measure.hpp and cpp/tests/unit_tests_benchmark_measure.cpp.
# Claim: an operation that fails inside a timed loop leaves the loop as an
# exception, so the lane aborts with the operation's error instead of timing
# the failure as a success, and the test that guards it dies when the check
# is taken out. The check is replaced by a discard of the operation's result
# in a scratch copy of the header; the one test unit that includes the header
# is recompiled with its own compile command, the scratch copy ahead of the
# tracked one on the include path, and linked into a scratch binary with the
# test binary's own link line, that one object swapped in. The test binary is
# built in a tree of the probe's own and the tracked tree is never written: a
# sweep, a hook or a commit reading it meanwhile would take a mutation there
# for the user's change. No real kernel can be made to fail mid-loop from
# outside, which is why the test drives the loops with a clock and an
# operation of its own and this probe proves the test is not vacuous.
# Non-zero exit: the benchmark cases pass with the check gone, or they do not
# pass with it in place. Exits 2 when cpp/build is not configured or a build
# fails.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
header=cpp/benchmarks/measure.hpp
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
tree=$scratch/cpp
tests=$tree/unit_tests

tools/private_cpp_tree.sh "$tree" unit_tests || exit 2
"$tests" "[benchmark]" > /dev/null 2>&1 || { echo "the benchmark cases fail before the mutation"; exit 1; }

# The three loops, the throughput one and the latency warmup and measured
# ones, check through the same line; a discard in any one is the defect, so
# all three are mutated and one surviving test is a pass.
grep -c 'require(op(.*), step);' "$header" | grep -qx 3 || {
    echo "the check is not written where this probe mutates it"
    exit 1
}
mkdir -p "$scratch/benchmarks" || exit 2
sed -e 's/require(op(\(.*\)), step);/std::ignore = op(\1);/' \
    -e 's/#include <vector>/#include <tuple>\n#include <vector>/' \
    "$header" > "$scratch/benchmarks/measure.hpp" || exit 2

# `#include "measure.hpp"` searches the including file's directory first,
# which holds no measure.hpp, then the include path in order, so the scratch
# directory placed first shadows the tracked header.
python/.venv/bin/python - "$scratch" "$tree" <<'PY' || exit 2
import json
import shlex
import subprocess
import sys
from pathlib import Path

scratch, tree = Path(sys.argv[1]), Path(sys.argv[2])
unit = "cpp/tests/unit_tests_benchmark_measure.cpp"
entry = next(e for e in json.loads((tree / "compile_commands.json").read_text(encoding="utf-8"))
             if e["file"].endswith("/" + unit))
argv = shlex.split(entry["command"])
obj = argv[argv.index("-o") + 1]
argv[argv.index("-o") + 1] = str(scratch / "measure.o")
argv.insert(1, f"-I{scratch / 'benchmarks'}")
subprocess.run(argv, cwd=entry["directory"], check=True)

link = shlex.split((tree / "CMakeFiles/unit_tests.dir/link.txt").read_text(encoding="utf-8"))
link[link.index(obj)] = str(scratch / "measure.o")
link[link.index("-o") + 1] = str(scratch / "unit_tests")
subprocess.run(link, cwd=tree, check=True)
PY
# A scratch binary that could not run at all would also exit non-zero, so the
# verdict is read from the test framework's own summary.
if "$scratch/unit_tests" "[benchmark]" > "$scratch/mutated.txt" 2>&1; then
    echo "the benchmark cases pass with the check discarded"
    exit 1
fi
grep -qE '^test cases: .* [1-9][0-9]* failed' "$scratch/mutated.txt" || {
    echo "the mutated binary did not run its cases:"
    tail -3 "$scratch/mutated.txt" | sed 's/^/  /'
    exit 2
}
exit 0
