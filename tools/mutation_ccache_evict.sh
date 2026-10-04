#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Evicts from a C++ mutation lane's compiler cache every entry its run did not
# use, so the cache the lane saves is that run's working set.
#
# Usage: tools/mutation_ccache_evict.sh START
#   START  seconds since the epoch, taken after the lane restored the cache and
#          zeroed its counters, and before anything compiled.
#
# ccache refreshes the modification time of every entry a hit reads and writes
# every entry a miss makes, so once the build is done an entry modified before
# START is one the run did not use: a unit's object from before its source or
# headers changed, or every object from before a change to the plugin, the Mull
# configuration or the toolchain.  The age passed to ccache is one second longer
# than the run, so ccache's cutoff falls between START - 1 and START plus the
# time between this script reading the clock and ccache reading it, and an entry
# used after that stays.
#
# The cache is kept whole when a compile failed, in the compiler or in its
# preprocessor (a build that stopped partway, whose unreached units' entries are
# still good), and when the run compiled nothing (a lane that failed before its
# build); the next run on another commit that compiles and fails no compile
# evicts, a run on the same commit restoring that commit's cache by its exact
# key and neither evicting nor saving.  It prints ccache's version, the cache
# and this run's counters first, and the cache again after an eviction, so the
# size a build left and the cleanups ccache made when it reached the lane's cap
# stay readable in the log.
#
# Exits 1 when ccache does not report exactly once a counter this reads, or
# when an entry modified at START - 1 or earlier survives the eviction, which is
# an eviction that does not go by the time a hit refreshes; 2 on a usage error;
# and with the failing command's own status when ccache or find fails.
set -euo pipefail

start=${1:-}
[[ $start =~ ^[1-9][0-9]*$ ]] || { echo "usage: tools/mutation_ccache_evict.sh START (seconds since the epoch)" >&2; exit 2; }

ccache --version | head -n 1
stats=$(ccache --print-stats)
# One counter of this run's statistics, refused unless ccache reports it once.
counter() {
    awk -F'\t' -v key="$1" '$1 == key {value = $2; seen++} END {if (seen != 1) exit 1; print value}' <<< "$stats" ||
        { echo "::error::ccache --print-stats reports no single $1 counter" >&2; exit 1; }
}
direct=$(counter direct_cache_hit)
preprocessed=$(counter preprocessed_cache_hit)
misses=$(counter cache_miss)
failed=$(counter compile_failed)
unpreprocessed=$(counter preprocessor_error)
files=$(counter files_in_cache)
size=$(counter cache_size_kibibyte)
cleanups=$(counter cleanups_performed)
echo "before eviction: $files files, $size KiB; this run: $((direct + preprocessed)) hits," \
    "$misses misses, $failed failed compiles, $unpreprocessed preprocessor errors," \
    "$cleanups cleanups at the cap"

if ((failed + unpreprocessed > 0)); then
    echo "a compile failed, so the build may have stopped short of units whose entries are still good; the cache is saved whole"
    exit 0
fi
if ((direct + preprocessed + misses == 0)); then
    echo "this run compiled nothing, so the cache is saved as it was restored"
    exit 0
fi

ccache --evict-older-than "$(($(date +%s) - start + 1))s"

stats=$(ccache --print-stats)
files=$(counter files_in_cache)
size=$(counter cache_size_kibibyte)
echo "after eviction: $files files, $size KiB"

directory=$(ccache --get-config cache_dir)
# The run's own entries were all modified at START or later, so an entry from
# START - 1 or earlier is one the eviction, whose cutoff is no earlier, missed.
# The files are the entries as ccache lists them: two levels down, less the
# counters and the leftovers of an NFS client.
stale=$(find "$directory" -mindepth 3 -type f ! -name stats ! -name '.nfs*' \
    ! -newermt "@$((start - 1))" | wc -l)
if ((stale > 0)); then
    echo "::error::$stale cache entries modified before this run survived the eviction" >&2
    exit 1
fi
