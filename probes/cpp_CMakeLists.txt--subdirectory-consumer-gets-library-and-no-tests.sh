#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: a parent project that add_subdirectory()s cpp/ can link
# aletheia::aletheia-cpp and gets no test targets and no Catch2 fetch, while
# the standalone configure registers the test suite. Non-zero exit: the alias
# is missing, a test target leaks into the consumer, Catch2 gets fetched for
# the consumer, or the standalone tree registers no tests. Exits 2 when
# cpp/build, whose fetched sources both configures read, is not configured.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
here=$(pwd)
scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/src" || exit 2
cat > "$scratch/CMakeLists.txt" <<CMAKE
cmake_minimum_required(VERSION 3.25)
project(consumer LANGUAGES CXX)
add_subdirectory($here/cpp aletheia-cpp)
add_executable(consumer src/main.cpp)
target_link_libraries(consumer PRIVATE aletheia::aletheia-cpp)
CMAKE
cat > "$scratch/src/main.cpp" <<CPP
#include <aletheia/aletheia.hpp>
int main() { return 0; }
CPP
# Point FetchContent at the sources cpp/build fetched, every one but Catch2's,
# so nothing is downloaded and a Catch2 the consumer asks for shows as a fetch.
sources=()
for fetched in "$here"/cpp/build/_deps/*-src; do
    name=$(basename "$fetched" -src)
    [ "$name" = catch2 ] || sources+=("-DFETCHCONTENT_SOURCE_DIR_${name^^}=$fetched")
done
cmake -S "$scratch" -B "$scratch/build" -DCMAKE_CXX_COMPILER=clang++-23 \
    "${sources[@]}" > "$scratch/configure.log" 2>&1 || { tail -5 "$scratch/configure.log"; exit 1; }
targets=$(cmake --build "$scratch/build" --target help 2>/dev/null)
printf '%s\n' "$targets" | grep -q 'unit_tests' && { echo "unit_tests leaked into the consumer"; exit 1; }
printf '%s\n' "$targets" | grep -q 'aletheia-cpp' || { echo "library target missing"; exit 1; }
[ -e "$scratch/build/_deps/catch2-subbuild" ] && { echo "consumer configure fetched Catch2"; exit 1; }
# The standalone configure, in a tree of the probe's own: ctest writes into the tree it lists.
tools/private_cpp_tree.sh "$scratch/standalone" || exit 2
standalone=$(ctest --test-dir "$scratch/standalone" --show-only=json-v1 2>/dev/null | grep -c '"name"')
[ "$standalone" -ge 15 ]
