#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Configures the C++ project into a build tree of the caller's own and builds
# the targets named, so a probe builds and runs what it needs without writing
# cpp/build or any tree another probe reads.
#
#   tools/private_cpp_tree.sh <directory> [<target>...] [-- <cmake argument>...]
#
# A directory not yet configured is configured as CI configures cpp/build,
# with clang-23 and the project's default generator and build type, the cmake
# arguments passed after those. Every dependency comes from the sources
# cpp/build fetched, and fetching is off, so nothing reaches the network. The
# targets, when any are named, are built with the directory as ccache's base
# directory: a path inside the tree reaches the cache relative to it, so two
# private trees share every object and a rebuild in a fresh one is served
# from the cache.
# Exits 2 on a bad command line or when cpp/build holds no fetched sources,
# and otherwise with cmake's status, its output on stderr when it fails.
set -u
usage="usage: tools/private_cpp_tree.sh <directory> [<target>...] [-- <cmake argument>...]"
[ "$#" -ge 1 ] || { echo "$usage" >&2; exit 2; }
tree=$1
shift
targets=()
while [ "$#" -gt 0 ] && [ "$1" != -- ]; do
    targets+=("$1")
    shift
done
[ "$#" -eq 0 ] || shift
root=$(cd "$(dirname "$0")/.." && pwd)
log=$(mktemp) || exit 2
trap 'rm -f "$log"' EXIT
if [ ! -f "$tree/CMakeCache.txt" ]; then
    sources=()
    for fetched in "$root"/cpp/build/_deps/*-src; do
        [ -d "$fetched" ] || continue
        name=$(basename "$fetched" -src)
        sources+=("-DFETCHCONTENT_SOURCE_DIR_${name^^}=$fetched")
    done
    [ "${#sources[@]}" -gt 0 ] || { echo "private_cpp_tree: cpp/build has fetched no dependencies; configure it once" >&2; exit 2; }
    cmake -S "$root/cpp" -B "$tree" -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23 \
        -DFETCHCONTENT_FULLY_DISCONNECTED=ON "${sources[@]}" "$@" > "$log" 2>&1 \
        || { status=$?; cat "$log" >&2; exit "$status"; }
fi
[ "${#targets[@]}" -gt 0 ] || exit 0
tree=$(cd "$tree" && pwd)
CCACHE_BASEDIR=$tree cmake --build "$tree" --target "${targets[@]}" > "$log" 2>&1 \
    || { status=$?; cat "$log" >&2; exit "$status"; }
