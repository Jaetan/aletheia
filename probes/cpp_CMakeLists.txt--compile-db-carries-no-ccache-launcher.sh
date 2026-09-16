#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: enabling ccache through CMAKE_CXX_COMPILER_LAUNCHER leaves
# compile_commands.json free of any launcher token, so the clang-tidy gate
# that reads the database sees the bare compiler. Non-zero exit: ccache is on
# PATH, the configured build tree's database names it, or no database exists
# to check. Skipped (exit 0) when ccache is not installed, since the claim is
# then untestable here.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v ccache > /dev/null || { echo "ccache not installed, claim untestable"; exit 0; }
db=cpp/build/compile_commands.json
[ -f "$db" ] || { echo "no compile database at $db; configure cpp/build first"; exit 1; }
grep -q '^CCACHE_PROGRAM:FILEPATH=/' cpp/build/CMakeCache.txt || { echo "ccache not found by the configure in cpp/build"; exit 1; }
grep -q 'ccache' cpp/build/CMakeFiles/aletheia-cpp.dir/build.make || { echo "build rules carry no launcher, so the claim is vacuous"; exit 1; }
! grep -q 'ccache' "$db"
