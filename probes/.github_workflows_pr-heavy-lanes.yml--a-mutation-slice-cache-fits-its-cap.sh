#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes .github/workflows/pr-heavy-lanes.yml.
# Claim: the compiler-cache cap a C++ mutation lane sets, CCACHE_MAXSIZE, is at
# least four fresh caches of the largest slice, and a fresh slice's cache is the
# size the lane's comment records. The cap is the room a lane's cache has to
# hold the live generation of objects and the superseded ones a change to the
# plugin, the configuration or the toolchain leaves behind, and a cap below four
# working sets lets an approximate LRU trim live objects; a cap sized from a
# figure that has drifted is sized from nothing.
# Three builds: slice 1 of each tree, configured the way the lane configures a
# leg, compiled from cold into an empty cache, and the cache's own size counter
# read after. Each is held within a tolerance of the recorded figure, and the
# cap is held against four times the largest.
# Non-zero exit: the workflow sets no single cap, the cap is under four of the
# largest slice, or a slice's fresh cache is outside the recorded figure's
# tolerance. Skipped (exit 0) when ccache, clang-23 or the plugin is not
# installed, since the claim is then untestable.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v ccache > /dev/null || { echo "ccache not installed, claim untestable"; exit 0; }
command -v clang++-23 > /dev/null || { echo "clang++-23 not installed, claim untestable"; exit 0; }
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "plugin not installed, claim untestable"; exit 0; }
[ -x python/.venv/bin/python ] || { echo "python/.venv missing, claim untestable"; exit 0; }

workflow=.github/workflows/pr-heavy-lanes.yml
# Recorded, KiB as `ccache --print-stats` counts cache_size_kibibyte, each slice
# of the tree built from cold into an empty cache; the three slices of one tree
# read within 60 KiB of each other, so one per tree stands for the tree.
declare -A recorded=([leak]=24944 [plain]=26060 [address]=29696)
tolerance_percent=20
multiple=4

caps=$(sed -n 's/^ *echo "CCACHE_MAXSIZE=\([0-9]*\)M"$/\1/p' "$workflow")
[ "$(printf '%s\n' "$caps" | grep -c .)" -eq 1 ] ||
    { echo "the workflow sets $(printf '%s\n' "$caps" | grep -c .) caps of the form NNNM, expected one"; exit 1; }
cap_bytes=$((caps * 1000 * 1000))

scratch=$(mktemp -d) || exit 2
trap 'rm -rf "$scratch"' EXIT
tree=cpp/build/probe-scratch/slice-cache
rm -rf "$tree"

status=0
largest=0
for sanitizer in leak plain address; do
    build="$PWD/$tree/$sanitizer"
    if ! CCACHE_DIR="$scratch/ccache-$sanitizer" CCACHE_MAXSIZE="${caps}M" \
        PYTHONPATH=. python/.venv/bin/python - "$sanitizer" "$build" "$scratch" <<'PY' > "$scratch/build-$sanitizer.log" 2>&1
import sys
from pathlib import Path

from tools.mutation_cpp import CppLeg, CppTree, LegPaths, REPO_ROOT, _build_cpp_mutation_tree, leg_config

sanitizer, build, scratch = sys.argv[1:]
leg = CppLeg(CppTree(sanitizer), 1)
build_dir = Path(build)
artifact = Path(scratch) / f"artifact-{sanitizer}"
artifact.mkdir(exist_ok=True)
config = leg_config(leg, build_dir)
built = _build_cpp_mutation_tree("cmake", LegPaths(REPO_ROOT / "cpp", build_dir, artifact, config), leg)
if not isinstance(built, str):
    sys.stdout.write(built.raw_log[-2000:])
    sys.exit(1)
PY
    then
        echo "the $sanitizer slice did not build:"; tail -5 "$scratch/build-$sanitizer.log"; exit 1
    fi
    size=$(CCACHE_DIR="$scratch/ccache-$sanitizer" ccache --print-stats | awk -F'\t' '$1 == "cache_size_kibibyte" {print $2}')
    [ -n "$size" ] || { echo "ccache reported no cache_size_kibibyte for the $sanitizer slice"; exit 1; }
    want=${recorded[$sanitizer]}
    low=$((want * (100 - tolerance_percent) / 100))
    high=$((want * (100 + tolerance_percent) / 100))
    if [ "$size" -lt "$low" ] || [ "$size" -gt "$high" ]; then
        echo "the $sanitizer slice's fresh cache holds $size KiB, outside $low to $high KiB around the recorded $want"
        status=1
    else
        echo "$sanitizer slice: $size KiB, recorded $want"
    fi
    [ "$size" -gt "$largest" ] && largest=$size
done

needed=$((largest * 1024 * multiple))
if [ "$cap_bytes" -lt "$needed" ]; then
    echo "CCACHE_MAXSIZE=${caps}M is $cap_bytes bytes, under $multiple caches of the largest slice ($largest KiB, $needed bytes)"
    status=1
else
    echo "cap ${caps}M holds $multiple caches of the largest slice ($largest KiB)"
fi
rm -rf "$tree"
exit "$status"
