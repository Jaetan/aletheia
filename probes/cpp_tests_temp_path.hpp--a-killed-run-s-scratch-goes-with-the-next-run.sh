#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/temp_path.hpp.
# Claim: a run killed before static destruction keeps its scratch directory,
# the next run removes it, and a directory whose owner still holds its lock is
# left where it is. The suite's own cases take both locks inside one process,
# which proves the descriptors are independent but not that a dead process
# releases; only two processes show that, which is what this drives.
# Non-zero exit: a killed run's scratch outlives its successor, a live owner's
# scratch is taken, or a clean run leaves its own behind.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/temp-path-reap
rm -rf "$scratch" && mkdir -p "$scratch/tmp" || exit 2
cat > "$scratch/driver.cpp" <<'CPP'
#include "temp_path.hpp"

#include <csignal>
#include <cstdio>

// Prints the scratch directory it owns, then either ends normally or dies the
// way a mutant run mull kills does, without reaching static destruction.
auto main(int argc, char** argv) -> int {
    std::puts(aletheia::test::scratch_dir().c_str());
    (void)std::fflush(stdout);
    if (argc > 1)
        (void)std::raise(SIGKILL);
    return 0;
}
CPP
clang++-23 -std=c++23 -Icpp/tests -o "$scratch/driver" "$scratch/driver.cpp" > "$scratch/compile.log" 2>&1 ||
    { tail -5 "$scratch/compile.log"; exit 1; }

TMPDIR="$PWD/$scratch/tmp"
export TMPDIR

killed=$("$scratch/driver" kill)
[ -d "$killed" ] || { echo "a killed run left no scratch directory, so nothing is under test"; exit 1; }

held="$TMPDIR/aletheia-cpp-tests-999999"
mkdir -p "$held" || exit 2
exec 9< "$held" || exit 2
flock -n 9 || { echo "cannot hold the lock on $held"; exit 2; }

survivor=$("$scratch/driver")
[ "$killed" != "$survivor" ] || { echo "the two runs shared a process id, so the removal is not attributable"; exit 2; }
[ -d "$killed" ] && { echo "the killed run's scratch outlived the next run: $killed"; exit 1; }
[ -d "$held" ] || { echo "a scratch directory whose owner holds its lock was removed: $held"; exit 1; }
exec 9<&-
[ -d "$survivor" ] && { echo "a run that ended normally left its scratch behind: $survivor"; exit 1; }
exit 0
