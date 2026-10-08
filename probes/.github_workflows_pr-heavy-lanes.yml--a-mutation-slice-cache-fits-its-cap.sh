#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes .github/workflows/pr-heavy-lanes.yml.
# Claim: the compiler-cache cap a C++ mutation lane sets, CCACHE_MAXSIZE, is at
# least three fresh caches of a slice of the mutation tree, and a fresh slice's
# cache is the size recorded here. A lane evicts what its run did not use unless
# the run compiled nothing, a compile failed, or the eviction failed or did not
# run, so the cache it restores is one working set plus, for each run since the
# last eviction that failed a compile or its eviction, at most one more, a whole
# set only when that run missed every object, and three covers one such run; a
# build that misses every object, after a change to the plugin, the
# configuration or the toolchain, holds those beside its own until the eviction,
# and a cap below the three lets an approximate LRU trim the build's own
# objects. A cap sized from a figure that has drifted is sized from nothing.
# One build: slice 1 of the tree, configured the way the lane configures a leg,
# compiled from cold into an empty cache, and the cache's own size counter read
# after. It is held within a tolerance of the recorded figure, and the cap is
# held against three times it.
# Non-zero exit: the workflow sets no single cap, the slice does not build or
# ccache reports no size for it, the cap is under three of the slice, or the
# slice's fresh cache is outside the recorded figure's tolerance; 2 when the
# repository root cannot be entered or the scratch directory cannot be made.
# Skipped (exit 0) when ccache, clang++-23, the plugin or python/.venv is
# missing, since the claim is then untestable.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v ccache > /dev/null || { echo "ccache not installed, claim untestable"; exit 0; }
command -v clang++-23 > /dev/null || { echo "clang++-23 not installed, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "plugin not installed, claim untestable"; exit 0; }
[ -x python/.venv/bin/python ] || { echo "python/.venv missing, claim untestable"; exit 0; }

workflow=.github/workflows/pr-heavy-lanes.yml
# Recorded, KiB as `ccache --print-stats` counts cache_size_kibibyte, slice 1 of
# the tree built from cold into an empty cache; the three slices read within
# 192 KiB of each other, so slice 1 stands for the three.
recorded=27712
tolerance_percent=20
multiple=3

caps=$(sed -n 's/^ *echo "CCACHE_MAXSIZE=\([0-9]*\)M"$/\1/p' "$workflow")
[ "$(printf '%s\n' "$caps" | grep -c .)" -eq 1 ] ||
    { echo "the workflow sets $(printf '%s\n' "$caps" | grep -c .) caps of the form NNNM, expected one"; exit 1; }
cap_bytes=$((caps * 1000 * 1000))

scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
build=$scratch/slice-cache

status=0
if ! CCACHE_DIR="$scratch/ccache" CCACHE_MAXSIZE="${caps}M" \
    PYTHONPATH=. python/.venv/bin/python - "$build" "$scratch" <<'PY' > "$scratch/build.log" 2>&1
import sys
from pathlib import Path

from tools.mutation_cpp import LegPaths, build_cpp_mutation_tree, cpp_sweep_directory
from tools.mutation_cpp_config import leg_config
from tools.mutation_cpp_legs import CppLeg

build, scratch = sys.argv[1:]
leg = CppLeg(1)
build_dir = Path(build)
artifact = Path(scratch) / "artifact"
artifact.mkdir(exist_ok=True)
config = leg_config(leg, build_dir)
built = build_cpp_mutation_tree("cmake", LegPaths(cpp_sweep_directory(), build_dir, artifact, config))
if not isinstance(built, str):
    sys.stdout.write(built.raw_log[-2000:])
    sys.exit(1)
PY
then
    echo "the slice did not build:"; tail -5 "$scratch/build.log"; exit 1
fi
size=$(CCACHE_DIR="$scratch/ccache" ccache --print-stats | awk -F'\t' '$1 == "cache_size_kibibyte" {print $2}')
[ -n "$size" ] || { echo "ccache reported no cache_size_kibibyte for the slice"; exit 1; }
low=$((recorded * (100 - tolerance_percent) / 100))
high=$((recorded * (100 + tolerance_percent) / 100))
if [ "$size" -lt "$low" ] || [ "$size" -gt "$high" ]; then
    echo "the slice's fresh cache holds $size KiB, outside $low to $high KiB around the recorded $recorded"
    status=1
else
    echo "slice: $size KiB, recorded $recorded"
fi

needed=$((size * 1024 * multiple))
if [ "$cap_bytes" -lt "$needed" ]; then
    echo "CCACHE_MAXSIZE=${caps}M is $cap_bytes bytes, under $multiple caches of the slice ($size KiB, $needed bytes)"
    status=1
else
    echo "cap ${caps}M holds $multiple caches of the slice ($size KiB)"
fi
exit "$status"
