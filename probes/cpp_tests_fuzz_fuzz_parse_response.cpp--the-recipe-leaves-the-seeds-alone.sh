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
# comment that goes back to naming the seed directory alone makes this probe's
# run write among the seeds and fail. The run is in a scratch copy of the
# seeds, compared afterwards with the tracked ones. Non-zero exit: the
# comment's own invocation leaves files behind among the seeds.
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

# The recipe's paths are from cpp/, so it runs from a scratch copy of the
# directories it names: the tracked seeds, and a fuzz tree of the probe's own
# configured and built as the comment's two cmake lines do, with the sources
# cpp/build fetched.
root=$PWD
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
git ls-files -z -- cpp/tests/fuzz/seed | xargs -0 cp --parents -t "$scratch" || exit 2
tools/private_cpp_tree.sh "$scratch/cpp/build-fuzz" fuzz_parse_response -- -DALETHEIA_FUZZ=ON || {
    echo "the configure and build lines the comment gives do not run"
    exit 1
}
cd "$scratch/cpp" || exit 2
mkdir -p "$first" || {
    echo "the write target the comment gives cannot be created"
    exit 1
}
# shellcheck disable=SC2086  # the comment's arguments are several paths
./build-fuzz/fuzz_parse_response -max_total_time=1 $args > /dev/null 2>&1 || {
    echo "the run line the comment gives does not run"
    exit 1
}

left=$(diff -rq "$root/cpp/tests/fuzz/seed" tests/fuzz/seed | wc -l)
[ "$left" -eq 0 ] || {
    echo "the run left $left difference(s) in the seed directories:"
    diff -rq "$root/cpp/tests/fuzz/seed" tests/fuzz/seed | head -5
    exit 1
}
exit 0
