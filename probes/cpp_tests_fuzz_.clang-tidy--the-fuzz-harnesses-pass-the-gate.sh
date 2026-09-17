#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/fuzz and its configuration.
# Claim: the libFuzzer harnesses hold to the same lint gate as the rest of the
# test tree. They compile only under the fuzz configuration, so the orchestrator
# step, which reads the ordinary build's compile database, cannot reach them;
# this probe runs the same gate against the fuzz database instead. Non-zero
# exit: a harness carries a finding, or the fuzz tree cannot be configured.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v run-clang-tidy-23 > /dev/null || { echo "run-clang-tidy-23 not installed"; exit 0; }
cd cpp || exit 2
if [ ! -f build-fuzz/compile_commands.json ]; then
    cmake -B build-fuzz -DALETHEIA_FUZZ=ON \
        -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23 > /dev/null 2>&1 || {
        echo "the fuzz tree cannot be configured"
        exit 2
    }
fi
out=$(run-clang-tidy-23 -quiet -p build-fuzz cpp/tests/fuzz/ 2>&1)
found=$(printf '%s\n' "$out" | grep -cE '(warning|error):')
if [ "$found" -ne 0 ]; then
    echo "the fuzz harnesses carry $found findings:"
    printf '%s\n' "$out" | grep -E '(warning|error):' | head -5
    exit 1
fi
exit 0
