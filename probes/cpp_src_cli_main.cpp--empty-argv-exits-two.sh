#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/src/cli/main.cpp.
# Claim: the aletheia-cli binary started with an empty argument vector (argc
# zero, which execve permits) behaves as with no subcommand: it prints the
# usage and exits 2 rather than reading past argv. Shown through a launcher
# that execs the binary with an empty argv. Builds the binary first.
# Non-zero exit: the process crashes or exits with another code. Exits 2 when
# cpp/build is not configured.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -f cpp/build/CMakeCache.txt ] || exit 2
cmake --build cpp/build --target aletheia-cli > /dev/null 2>&1 || exit 2
scratch=cpp/build/probe-scratch/cli-empty-argv
mkdir -p "$scratch" || exit 2
cat > "$scratch/launch.cpp" <<'CPP'
#include <unistd.h>
int main(int, char** argv) {
    char* empty[] = {nullptr};
    execv(argv[1], empty);
    return 99;
}
CPP
clang++-23 -std=c++23 "$scratch/launch.cpp" -o "$scratch/launch" > "$scratch/compile.log" 2>&1 || { tail -3 "$scratch/compile.log"; exit 1; }
"$scratch/launch" "$PWD/cpp/build/aletheia-cli" > "$scratch/out.txt" 2> "$scratch/err.txt"; rc=$?
[ "$rc" -eq 2 ] && grep -q 'Usage: aletheia-cli' "$scratch/err.txt" || { echo "rc=$rc"; head -2 "$scratch/err.txt"; exit 1; }
