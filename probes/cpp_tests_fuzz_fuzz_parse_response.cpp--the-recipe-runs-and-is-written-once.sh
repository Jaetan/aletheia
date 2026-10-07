#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/fuzz/fuzz_parse_response.cpp and cpp/CMakeLists.txt.
# Claim: the fuzz build-and-run recipe is written once, in the harness the
# other three point at, and the lines it gives run. The probe checks the
# comment gives the commands and runs them, with a one-second corpus pass in
# place of the documented sixty. Non-zero exit:
# the recipe is written in the build file too, a harness stops pointing at
# the owner, or a command the comment gives does not run.
set -u
cd "$(dirname "$0")/.." || exit 2
owner=cpp/tests/fuzz/fuzz_parse_response.cpp
status=0

command -v clang-23 > /dev/null && command -v clang++-23 > /dev/null || {
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
            'mkdir -p build-fuzz/corpus/parse_response' \
            './build-fuzz/fuzz_parse_response -max_total_time=60' \
            'build-fuzz/corpus/parse_response tests/fuzz/seed/parse_response/'; do
    grep -qF "$line" "$owner" || {
        echo "the comment no longer gives: $line"
        status=1
    }
done
[ "$status" -eq 0 ] || exit "$status"

# The recipe's paths are from cpp/, so it runs from a scratch copy of the
# directories it names: the tracked seeds, and a fuzz tree of the probe's own
# configured and built as the comment's two cmake lines do, with the sources
# cpp/build fetched.
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
git ls-files -z -- cpp/tests/fuzz/seed | xargs -0 cp --parents -t "$scratch" || exit 2
tools/private_cpp_tree.sh "$scratch/cpp/build-fuzz" fuzz_parse_response -- -DALETHEIA_FUZZ=ON || {
    echo "the configure and build lines the comment gives do not run"
    exit 1
}
cd "$scratch/cpp" || exit 2
mkdir -p build-fuzz/corpus/parse_response || {
    echo "the mkdir line the comment gives does not run"
    exit 1
}
./build-fuzz/fuzz_parse_response -max_total_time=1 \
    build-fuzz/corpus/parse_response tests/fuzz/seed/parse_response/ > /dev/null 2>&1 || {
    echo "the run line the comment gives does not run"
    exit 1
}
exit 0
