#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: the -ffile-prefix-map flag is withheld from the mutation build because
# the installed Mull IR plugin resolves the mapped source path relative to the
# compiler's working directory and crashes clang (exit 139) when it does not
# exist there, which is the case in every CMake build directory. This probe
# holds while that is still so: it compiles one library source from a scratch
# directory with the plugin and the flag and passes when clang fails that way.
# Non-zero exit: the compile succeeded, so the plugin no longer crashes and
# CMakeLists.txt can apply the flag to the mutation build too. Skipped (exit 0)
# when the plugin is not installed, since the claim is then untestable here.
set -u
cd "$(dirname "$0")/.." || exit 2
plugin=$HOME/.local/bin/mull-ir-frontend-23
[ -x "$plugin" ] || { echo "plugin not installed, claim untestable"; exit 0; }
scratch=cpp/build/probe-scratch/prefixmap
mkdir -p "$scratch" || exit 2
root=$(pwd)
cd "$scratch" || exit 2
# clang runs the compiler in its own process, so the plugin's crash is the
# driver's own signal: the shell reports 128 plus SIGSEGV, which is 139.
clang++-23 -std=c++23 "-fpass-plugin=$plugin" -g -O0 "-ffile-prefix-map=$root=." \
    -I"$root/cpp/include" -I"$root/cpp/src" -c "$root/cpp/src/types.cpp" -o types.o > compile.log 2>&1
status=$?
if [ "$status" -eq 0 ]; then
    echo "plugin now accepts -ffile-prefix-map; drop the exclusion in cpp/CMakeLists.txt"
    exit 1
fi
[ "$status" -eq 139 ] || grep -q 'exit code 139' compile.log
