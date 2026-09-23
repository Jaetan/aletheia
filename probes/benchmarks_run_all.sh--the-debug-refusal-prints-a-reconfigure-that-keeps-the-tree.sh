#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes benchmarks/run_all.sh.
# Claim: the reconfigure the runner prints when it refuses a Debug-configured
# cpp/build is a plain cmake configure with -DCMAKE_BUILD_TYPE=Release, and
# that command alone turns a Debug cache into a Release one. The hint used to
# open with rm -rf cpp/build, which throws away the fetched dependencies and
# makes the reconfigure need the network, for a change a cache variable
# carries. Shown on a scratch CMake project with no compiler, the hint's own
# command with its paths swapped for the scratch ones.
# Non-zero exit: the hint has a clean in it, is not the one command, or does
# not flip a Debug cache to Release when run.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v cmake >/dev/null || exit 2
dir=$(mktemp -d) || exit 2
trap 'rm -rf "$dir"' EXIT
status=0
# The whole of the line the runner prints after "Reconfigure with", less its
# indentation, so a clean in front of the cmake call is seen.
hint=$(sed -n '/Reconfigure with/{n;s/.*echo "\(.*\)" >&2.*/\1/p}' benchmarks/run_all.sh | sed 's/^ *//')
case "$hint" in
    "cmake -S cpp -B cpp/build"*) ;;
    *) echo "the runner prints no cmake -S cpp -B cpp/build reconfigure: '$hint'"; status=1 ;;
esac
grep -q 'rm ' <<< "$hint" && { echo "the hint cleans the tree: $hint"; status=1; }
grep -qE '&&|;|\|' <<< "$hint" && { echo "the hint is more than one command: $hint"; status=1; }
grep -q -- '-DCMAKE_BUILD_TYPE=Release' <<< "$hint" || { echo "the hint does not set the build type: $hint"; status=1; }
# Nothing below runs a hint whose shape failed a check above, and the shape
# is one configure call with -D options and nothing else: an unchecked hint
# is run as printed, and one that opens with a clean removes cpp/build.
[ "$status" -eq 0 ] || exit 1
grep -qE '^cmake -S cpp -B cpp/build( -D[A-Z_]+=[A-Za-z0-9]+)*$' <<< "$hint" || { echo "not one configure call: $hint"; exit 1; }
mkdir -p "$dir/src" || exit 2
printf 'cmake_minimum_required(VERSION 3.25)\nproject(scratch NONE)\n' > "$dir/src/CMakeLists.txt"
cmake -S "$dir/src" -B "$dir/build" -DCMAKE_BUILD_TYPE:STRING=Debug > "$dir/debug.log" 2>&1 || { echo "the Debug configure failed"; tail -3 "$dir/debug.log"; exit 2; }
grep -q '^CMAKE_BUILD_TYPE:[A-Z]*=Debug$' "$dir/build/CMakeCache.txt" || { echo "the scratch cache is not Debug"; exit 2; }
swapped=${hint/-S cpp -B cpp\/build/-S "$dir/src" -B "$dir/build"}
eval "$swapped" > "$dir/release.log" 2>&1 || { echo "the hint failed to run"; tail -3 "$dir/release.log"; status=1; }
grep -q '^CMAKE_BUILD_TYPE:[A-Z]*=Release$' "$dir/build/CMakeCache.txt" || { echo "the hint left the cache at $(grep '^CMAKE_BUILD_TYPE' "$dir/build/CMakeCache.txt")"; status=1; }
exit $status
