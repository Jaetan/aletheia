#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the cmake-lint step in tools/_ci_steps.py.
# Claim: the gate lints the tree's CMake files and fails on a violation. Its
# config option takes one or more values, so without the `--` separator the
# tool swallows the file paths as configuration files, scans nothing, prints
# "files scanned: 0" and exits zero. That shape is why this probe asserts the
# count as well as the exit.
# Non-zero exit: the gate scans nothing, or a violation does not fail it.
set -eu
root=$(git rev-parse --show-toplevel)
cd "$root"
lint=python/.venv/bin/cmake-lint
[ -x "$lint" ] || lint=$(command -v cmake-lint) || exit 2

cmd="git ls-files -z -- 'CMakeLists.txt' '*/CMakeLists.txt' '*.cmake' '*.cmake.in' | xargs -0 -r cmake-lint -c .cmake-format.yaml --"
grep -qE "xargs -0 -r \{shlex.quote\(cmake_lint_bin\)\} -c .cmake-format.yaml --" tools/_ci_steps.py || {
    echo "FAIL: the gate's command is not the one this probe checks"
    exit 1
}

out=$(eval "$cmd" 2>&1) || {
    echo "FAIL: the gate is not clean on the tree it lints"
    echo "$out" | head -5
    exit 1
}
scanned=$(printf '%s\n' "$out" | sed -n 's/^files scanned: //p')
[ -n "$scanned" ] && [ "$scanned" -gt 0 ] || {
    echo "FAIL: the gate scanned $scanned files, so it could not have failed"
    exit 1
}

# Teeth: a violation must fail it.
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
printf 'cmake_minimum_required(VERSION 3.25)\nif(TRUE)\n  set(x 1)\nendif()\n' > "$scratch/CMakeLists.txt"
if "$lint" -c .cmake-format.yaml -- "$scratch/CMakeLists.txt" > /dev/null 2>&1; then
    echo "FAIL: a file with the wrong indentation did not fail the gate"
    exit 1
fi

echo "PASS: the gate scans $scanned files and fails on a violation"
