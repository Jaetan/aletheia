#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: a parent project that add_subdirectory()s cpp/ can link
# aletheia::aletheia-cpp and gets no test targets and no Catch2 fetch, while
# the standalone configure registers the test suite. Non-zero exit: the alias
# is missing, a test target leaks into the consumer, Catch2 gets fetched for
# the consumer, or the standalone tree registers no tests.
set -u
cd "$(dirname "$0")/.." || exit 2
here=$(pwd)
scratch=cpp/build/probe-scratch/subdir-consumer
rm -rf "$scratch"; mkdir -p "$scratch/src" || exit 2
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
# Point FetchContent at the sources the standalone tree already fetched, so
# nothing is downloaded and the standalone tree's own sub-builds are untouched.
deps=$here/cpp/build/_deps
cmake -S "$scratch" -B "$scratch/build" -DCMAKE_CXX_COMPILER=clang++-23 \
    -DFETCHCONTENT_SOURCE_DIR_JSON="$deps/json-src" \
    -DFETCHCONTENT_SOURCE_DIR_YAML-CPP="$deps/yaml-cpp-src" \
    -DFETCHCONTENT_SOURCE_DIR_OPENXLSX="$deps/openxlsx-src" > "$scratch/configure.log" 2>&1 || { tail -5 "$scratch/configure.log"; exit 1; }
targets=$(cmake --build "$scratch/build" --target help 2>/dev/null)
printf '%s\n' "$targets" | grep -q 'unit_tests' && { echo "unit_tests leaked into the consumer"; exit 1; }
printf '%s\n' "$targets" | grep -q 'aletheia-cpp' || { echo "library target missing"; exit 1; }
[ -e "$scratch/build/_deps/catch2-subbuild" ] && { echo "consumer configure fetched Catch2"; exit 1; }
standalone=$(ctest --test-dir cpp/build --show-only=json-v1 2>/dev/null | grep -c '"name"')
[ "$standalone" -ge 15 ]
