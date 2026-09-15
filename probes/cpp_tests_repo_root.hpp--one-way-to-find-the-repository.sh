#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the test tree's repository-root discovery.
# Claim: a test finds the repository one way, from the environment ctest
# passes it, and no test walks up from its own source path, which bakes the
# build machine's layout into the binary. Every target whose source asks for
# the root is given it by ctest, and a binary run without it refuses loudly
# instead of guessing. Non-zero exit: a source walks from __FILE__, a target
# asks for the root without being given it, or a binary run without it
# passes anyway.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

# Code, not prose: a line that mentions the macro behind a comment marker is
# this header explaining why nobody should use it.
walkers=$(grep -lE '^[[:space:]]*[^/[:space:]].*__FILE__' cpp/tests/*.cpp cpp/tests/*.hpp 2>/dev/null || true)
[ -z "$walkers" ] || {
    echo "a test source still walks up from its own path:"
    printf '%s\n' "$walkers"
    status=1
}

# Every source asking for the root belongs to a target ctest gives it to.
for src in $(grep -l 'repo_root()' cpp/tests/*.cpp 2>/dev/null); do
    stem=$(basename "$src" .cpp)
    target=$(grep -oE "add_executable\([A-Za-z0-9_]+ [^)]*tests/$stem\.cpp" cpp/CMakeLists.txt |
        head -1 | sed -E 's/add_executable\(([A-Za-z0-9_]+).*/\1/')
    [ -n "$target" ] || continue
    grep -A2 "set_tests_properties($target PROPERTIES" cpp/CMakeLists.txt |
        grep -q 'ALETHEIA_TEST_REPO_ROOT' || {
        echo "$target asks for the repository root and ctest does not pass it"
        status=1
    }
done

binary=cpp/build/dbc_corpus_parity_tests
if [ -x "$binary" ]; then
    if env -u ALETHEIA_REPO_ROOT "./$binary" > /dev/null 2>&1; then
        echo "a binary run without the variable passed, so it guessed a root"
        status=1
    fi
fi
exit $status
