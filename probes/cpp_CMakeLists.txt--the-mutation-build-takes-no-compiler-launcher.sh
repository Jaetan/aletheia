#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/CMakeLists.txt.
# Claim: a mutation build runs the compiler bare, with no ccache launcher, even
# where ccache is on PATH. The Mull plugin's output depends on the plugin binary
# and on cpp/mull.yml, and ccache hashes neither, so a launched compile replays
# an earlier configuration's mutants and its stderr: measured before the fix, a
# clean rebuild after adding cpp/mull.yml produced the same 62 mutants and
# printed the plugin's "cannot find config" from the cache. Non-zero exit: the
# configured mutation tree's build rules name ccache. Skipped (exit 0) when
# ccache or the plugin is not installed, since the claim is then untestable.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v ccache > /dev/null || { echo "ccache not installed, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "plugin not installed, claim untestable"; exit 0; }
tree=cpp/build/probe-scratch/mutation-launcher
rm -rf "$tree"
cmake -S cpp -B "$tree" -DALETHEIA_MUTATION=ON -DCMAKE_C_COMPILER=clang-23 \
    -DCMAKE_CXX_COMPILER=clang++-23 > "$tree.log" 2>&1 || { echo "configure failed, see $tree.log"; exit 1; }
grep -q '^CCACHE_PROGRAM:FILEPATH=/' "$tree/CMakeCache.txt" || { echo "ccache not found by the configure, claim vacuous"; exit 1; }
if grep -rq 'ccache' "$tree/CMakeFiles/aletheia-cpp.dir/build.make" "$tree/CMakeFiles/unit_tests.dir/build.make"; then
    echo "the mutation build's rules name ccache"
    exit 1
fi
echo "PASS: the mutation build runs the compiler bare"
