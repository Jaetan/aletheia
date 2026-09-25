#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/tests/temp_path.hpp.
# Claim: a process whose scratch directory a peer is removing at the moment
# of the first scratch_dir() call holds that directory once the peer is done,
# however long the removal takes. The peer holds the directory's lock for the
# whole removal, tens of milliseconds for a populated directory, and a thread
# of the same process stands in for it because flock is per open file
# description. The directory is populated so that a fixture waiting on time
# rather than on the lock reads red: an empty directory's removal takes
# microseconds, and 20000 files take about 45 ms to remove.
# Non-zero exit: the first call threw, or answered a path that does not exist.
set -u
cd "$(dirname "$0")/.." || exit 2
scratch=cpp/build/probe-scratch/temp-path-peer
rm -rf "$scratch" && mkdir -p "$scratch/tmp" || exit 2
cat > "$scratch/driver.cpp" <<'CPP'
#include "temp_path.hpp"

#include <cstdio>
#include <fstream>
#include <latch>
#include <optional>
#include <thread>

// A peer thread holds the lock on the directory this process's first
// scratch_dir() call will want, populated, and removes it under the lock
// while the main thread makes that call.
auto main() -> int {
    auto const dir = std::filesystem::temp_directory_path() /
                     (std::string(aletheia::test::scratch_prefix) + std::to_string(::getpid()));
    std::latch held{1};
    bool peer_held = false;
    std::jthread peer{[&] {
        std::optional<aletheia::test::ScratchLock> lock;
        aletheia::test::hold_scratch_dir(dir, lock);
        peer_held = lock->owns(dir);
        std::ranges::for_each(std::views::iota(0, 20000), [&dir](int i) {
            std::ofstream{dir / std::to_string(i)} << "x";
        });
        held.count_down();
        std::error_code ec;
        std::filesystem::remove_all(dir, ec);
    }};
    held.wait();
    auto const& got = aletheia::test::scratch_dir();
    peer.join();
    if (!peer_held) {
        std::puts("the peer could not take the lock, so nothing was contested");
        return 2;
    }
    if (got != dir || !std::filesystem::is_directory(got)) {
        std::printf("scratch_dir answered %s, which is not the directory at %s\n", got.c_str(), dir.c_str());
        return 1;
    }
    return 0;
}
CPP
clang++-23 -std=c++23 -Icpp/tests -o "$scratch/driver" "$scratch/driver.cpp" > "$scratch/compile.log" 2>&1 ||
    { tail -5 "$scratch/compile.log"; exit 1; }

TMPDIR="$PWD/$scratch/tmp"
export TMPDIR

for run in 1 2 3; do
    "$scratch/driver" > "$scratch/run-$run.log" 2>&1
    rc=$?
    [ "$rc" -eq 0 ] || { echo "run $run: exit $rc"; cat "$scratch/run-$run.log"; exit "$rc"; }
done
left=$(find "$TMPDIR" -mindepth 1 -maxdepth 1 | wc -l)
[ "$left" -eq 0 ] || { echo "a run that ended normally left $left entries behind"; ls "$TMPDIR"; exit 1; }
exit 0
