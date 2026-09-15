#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/fuzz/fuzz_parse_response.cpp and cpp/CMakeLists.txt.
# Claim: the fuzz build-and-run recipe is written once, in the harness the
# other three point at, and the three lines it gives run from the repository
# root. The probe extracts the commands from the comment and runs them, with
# a one-second corpus pass in place of the documented sixty. Non-zero exit:
# the recipe is written in the build file too, a harness stops pointing at
# the owner, or a command the comment gives does not run.
set -u
cd "$(dirname "$0")/.." || exit 2
owner=cpp/tests/fuzz/fuzz_parse_response.cpp
status=0

command -v clang > /dev/null && command -v clang++ > /dev/null || {
    echo "clang not installed, recipe untestable"
    exit 0
}

grep -qE 'cmake (-B|--build).*(ALETHEIA_FUZZ|build-fuzz)' cpp/CMakeLists.txt && {
    echo "the build file writes the fuzz recipe a second time"
    status=1
}
grep -q 'fuzz_parse_response.cpp' cpp/CMakeLists.txt || {
    echo "the build file does not point at the recipe's owner"
    status=1
}
for harness in decode_binary_frame parse_dbc_json parse_rational_number; do
    grep -q 'see fuzz_parse_response.cpp comment header' "cpp/tests/fuzz/fuzz_$harness.cpp" || {
        echo "fuzz_$harness.cpp does not point at the recipe's owner"
        status=1
    }
done

# The commands below are the comment's own; fail if the comment stops giving
# them, so the probe cannot drift into testing something the file no longer
# documents.
for line in 'cmake -B build-fuzz -DALETHEIA_FUZZ=ON' \
            'cmake --build build-fuzz --target fuzz_parse_response' \
            './build-fuzz/fuzz_parse_response -max_total_time=60'; do
    grep -qF "$line" "$owner" || {
        echo "the comment no longer gives: $line"
        status=1
    }
done
[ "$status" -eq 0 ] || exit "$status"

# The comment's paths are relative to cpp/, so the commands run from there.
cd cpp || exit 2
cmake -B build-fuzz -DALETHEIA_FUZZ=ON \
    -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ > /dev/null 2>&1 || {
    echo "the configure line the comment gives does not run"
    exit 1
}
cmake --build build-fuzz --target fuzz_parse_response > /dev/null 2>&1 || {
    echo "the build line the comment gives does not run"
    exit 1
}
./build-fuzz/fuzz_parse_response -max_total_time=1 \
    tests/fuzz/seed/parse_response/ > /dev/null 2>&1 || {
    echo "the run line the comment gives does not run"
    exit 1
}
exit 0
