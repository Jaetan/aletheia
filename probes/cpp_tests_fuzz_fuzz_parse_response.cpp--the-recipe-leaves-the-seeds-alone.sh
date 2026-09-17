#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/fuzz/fuzz_parse_response.cpp.
# Claim: running the recipe the comment gives adds nothing to the tracked seed
# directories. libFuzzer writes every input it finds into the FIRST directory
# on its command line, so the comment must name a corpus directory under the
# ignored build-fuzz/ tree there and the seed directory only after it. The
# arguments are taken from the comment and run, rather than written here, so a
# comment that goes back to naming the seed directory alone makes this probe
# write into the tree and fail. Non-zero exit: the comment's own invocation
# leaves files behind under cpp/tests/fuzz/seed/.
set -u
cd "$(dirname "$0")/.." || exit 2
owner=cpp/tests/fuzz/fuzz_parse_response.cpp

command -v clang-23 > /dev/null && command -v clang++-23 > /dev/null || {
    echo "clang not installed, recipe untestable"
    exit 0
}

# The arguments are the comment's own: the line continuing the run command.
args=$(sed -n '/^\/\/ .*fuzz_parse_response -max_total_time=60 \\$/{n;s|^// *||;p;}' "$owner")
[ -n "$args" ] || {
    echo "the comment no longer continues its run line with the directories"
    exit 1
}
first=${args%% *}
case $first in
    build-fuzz/*) ;;
    *) echo "the comment gives $first as libFuzzer's write target, not a build-fuzz/ path"; exit 1 ;;
esac

cd cpp || exit 2
cmake -B build-fuzz -DALETHEIA_FUZZ=ON \
    -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23 > /dev/null 2>&1 || {
    echo "the configure line the comment gives does not run"
    exit 1
}
cmake --build build-fuzz --target fuzz_parse_response > /dev/null 2>&1 || {
    echo "the build line the comment gives does not run"
    exit 1
}
mkdir -p "$first" || {
    echo "the write target the comment gives cannot be created"
    exit 1
}
# shellcheck disable=SC2086  # the comment's arguments are several paths
./build-fuzz/fuzz_parse_response -max_total_time=1 $args > /dev/null 2>&1 || {
    echo "the run line the comment gives does not run"
    exit 1
}

left=$(git status --porcelain -- tests/fuzz/seed/ | wc -l)
[ "$left" -eq 0 ] || {
    echo "the run left $left file(s) in the tracked seed directories:"
    git status --porcelain -- tests/fuzz/seed/ | head -5
    exit 1
}
exit 0
