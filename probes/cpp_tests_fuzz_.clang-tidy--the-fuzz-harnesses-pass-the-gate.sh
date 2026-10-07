#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/fuzz and its configuration.
# Claim: the libFuzzer harnesses hold to the same lint gate as the rest of the
# test tree. They compile only under the fuzz configuration, so the orchestrator
# step, which reads the ordinary build's compile database, cannot reach them;
# this probe runs the same gate against the database of a fuzz tree it
# configures for itself. Non-zero exit: a harness carries a finding, or the
# fuzz tree cannot be configured.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v run-clang-tidy-23 > /dev/null || { echo "run-clang-tidy-23 not installed"; exit 0; }
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
tools/private_cpp_tree.sh "$scratch/build-fuzz" -- -DALETHEIA_FUZZ=ON || {
    echo "the fuzz tree cannot be configured"
    exit 2
}
out=$(run-clang-tidy-23 -quiet -p "$scratch/build-fuzz" cpp/tests/fuzz/ 2>&1)
found=$(printf '%s\n' "$out" | grep -cE '(warning|error):')
if [ "$found" -ne 0 ]; then
    echo "the fuzz harnesses carry $found findings:"
    printf '%s\n' "$out" | grep -E '(warning|error):' | head -5
    exit 1
fi
exit 0
