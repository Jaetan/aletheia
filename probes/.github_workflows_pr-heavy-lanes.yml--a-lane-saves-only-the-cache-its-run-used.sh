#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes .github/workflows/pr-heavy-lanes.yml and
# tools/mutation_ccache_evict.sh.
# Claim: a C++ mutation lane that builds saves the compiler-cache entries its
# run used and no other, and one that compiled nothing or failed a compile, in
# the compiler or in its preprocessor, saves its cache whole. The lane zeroes
# the counters and takes the time after it restores the cache and, under the
# save's own condition once that time was taken, runs the script with it before
# the save; ccache refreshes an entry's modification time on a hit, so what the
# build read or wrote stays and what it only restored goes.
# Three parts. The workflow is held to zero the counters and take the start
# after the restore and before the sweep, and to run the script after the sweep
# and before the save, each line exactly once, under the save's condition with
# the start's presence added. A stand-in for ccache and for date, which fix what
# each reports, holds the script's own arithmetic and refusals: the age it hands
# ccache is one second longer than the run, an entry modified at START - 1 that
# survives fails it and one at START - 0.5 does not, a counter ccache omits or
# reports twice fails it, and the cache it checks is the one ccache names as
# cache_dir. Then real ccache, the entries' modification times aged an hour
# before each arm and their access times set at the arm's start or later, so an
# eviction by access time would keep them: the leak tree's first slice built
# once, then rebuilt in direct mode beside one unit's entries it does not read
# (every slice entry kept, the unit's gone), rebuilt in preprocessor mode (every
# result kept, every manifest, which that mode does not read, gone), built under
# the second slice's configuration (its own entries kept, none of the first's),
# nothing compiled, one good compile beside one failed compile, and one good
# compile beside one preprocessor error (every entry kept in the last three);
# each arm also reads which way the script went.
# Non-zero exit: the workflow does not carry those lines once each, in that
# order and under that condition; a stand-in case does not end as named; a build
# fails or stores nothing; a real arm is not the case it names (a rebuild that
# misses or hits in the other mode, a second slice that hits, two units that are
# not one miss and one failure of the kind named and none of the other); the
# script exits non-zero or takes another branch than the arm names; or the cache
# after the script is not the one the arm names. Exits 2 when the repository
# root cannot be entered or the scratch directory cannot be made. The
# workflow's conditions are skipped when python/.venv is missing, and the
# real-ccache part, with the first two parts' verdict kept, when ccache,
# clang++-23, the plugin or python/.venv is missing, since each is then
# untestable.
set -u
cd "$(dirname "$0")/.." || exit 2

workflow=.github/workflows/pr-heavy-lanes.yml
script=tools/mutation_ccache_evict.sh
read -r start_line <<'LINE'
echo "MUTATION_CACHE_START=$(date +%s)" >> "${GITHUB_ENV}"
LINE
read -r evict_line <<'LINE'
run: tools/mutation_ccache_evict.sh "${MUTATION_CACHE_START}"
LINE
read -r sweep_name <<'LINE'
name: Mutation testing (${{ matrix.lane }})
LINE
# The line number of the one uncommented line holding the text given, or 0.
line_of() {
    local found
    found=$(grep -nF -- "$1" "$workflow" | grep -v '^[0-9]*:[[:space:]]*#' | cut -d: -f1)
    [ "$(printf '%s\n' "$found" | grep -c .)" -eq 1 ] || { echo "0"; return; }
    echo "$found"
}
restore=$(line_of 'name: Restore ccache (C++ mutation trees)')
zero=$(line_of 'ccache --zero-stats')
start=$(line_of "$start_line")
sweep=$(line_of "$sweep_name")
evict=$(line_of "$evict_line")
save=$(line_of 'name: Save ccache (C++ mutation trees)')
for name in restore zero start sweep evict save; do
    [ "${!name}" -gt 0 ] || { echo "the workflow does not carry the $name line exactly once"; exit 1; }
done
if ! { [ "$restore" -lt "$zero" ] && [ "$zero" -lt "$start" ] && [ "$start" -lt "$sweep" ] &&
    [ "$sweep" -lt "$evict" ] && [ "$evict" -lt "$save" ]; }; then
    echo "the lines are out of order: restore $restore, zero $zero, start $start, sweep $sweep, eviction $evict, save $save"
    exit 1
fi
# The step that runs the script runs under the save's condition with the
# start's presence added: a leg that swept and then failed saves, so it evicts
# first.  The conditions are read from the workflow as YAML, the step that runs
# the script found by its run and the save by its name, so no layout of the
# file can lend one step another's condition; a save's condition with an || in
# it is refused, since the start's presence appended to it would guard only its
# last arm.
if [ -x python/.venv/bin/python ]; then
    if python/.venv/bin/python - "$workflow" "${evict_line#run: }" <<'PY'; then
import sys

import yaml

workflow, script = sys.argv[1:]
with open(workflow, encoding="utf-8") as stream:
    jobs = yaml.safe_load(stream)["jobs"]
steps = [step for job in jobs.values() for step in job.get("steps", [])]
evicting = [step for step in steps if str(step.get("run", "")).strip() == script]
saving = [step for step in steps if step.get("name") == "Save ccache (C++ mutation trees)"]
if len(evicting) != 1 or len(saving) != 1:
    sys.exit(f"{len(evicting)} steps run the script and {len(saving)} save the cache, not one each")
save_if = str(saving[0].get("if") or "").strip()
evict_if = str(evicting[0].get("if") or "").strip()
if not save_if or not evict_if:
    sys.exit("the save or the step running the script has no condition of its own")
body = save_if.removeprefix("${{ ").removesuffix(" }}")
if body == save_if or len(body) + 7 != len(save_if) or "||" in body or "${{" in body or "}}" in body:
    sys.exit(f"the save's condition is not one conjunction in one expression: {save_if}")
expected = save_if.removesuffix(" }}") + " && env.MUTATION_CACHE_START != '' }}"
if evict_if != expected:
    sys.exit(f"the eviction's condition is not the save's with the start's presence added:\n"
             f"  save:     {save_if}\n  eviction: {evict_if}")
PY
        echo "workflow: the counters zeroed and the start taken after the restore, the script run before the save under its condition"
    else
        exit 1
    fi
else
    echo "python/.venv missing, the workflow's conditions are untestable"
fi

scratch=$(mktemp -d) || exit 2
tree=$scratch/evict-unused
trap 'rm -rf "$scratch"' EXIT
status=0
# Print an arm's line, and count it red unless its verdict is ok.
report() {
    echo "$2"
    [ "$1" = ok ] || status=1
}

# The stand-ins: ccache reports the counters in STUB_STATS, names STUB_DIR as
# its cache, and records the age it is asked to evict at without evicting;
# date reports STUB_NOW for +%s.
mkdir -p "$scratch/stub"
cat > "$scratch/stub/ccache" <<'STUB'
#!/usr/bin/env bash
case "$1" in
    --version) echo "ccache version stand-in" ;;
    --print-stats) cat "$STUB_STATS" ;;
    --get-config) [ "${2:-}" = cache_dir ] || exit 64; echo "$STUB_DIR" ;;
    --evict-older-than) echo "$2" > "$STUB_DIR.age" ;;
    *) exit 64 ;;
esac
STUB
cat > "$scratch/stub/date" <<'STUB'
#!/usr/bin/env bash
if [ "${1:-}" = +%s ]; then echo "$STUB_NOW"; else exec /usr/bin/date "$@"; fi
STUB
chmod +x "$scratch/stub/ccache" "$scratch/stub/date"
stub_now=2000000000
stub_start=$((stub_now - 100))
counters() {
    printf '%s\t%s\n' direct_cache_hit 1 preprocessed_cache_hit 0 cache_miss 0 compile_failed 0 \
        preprocessor_error 0 files_in_cache 1 cache_size_kibibyte 4 cleanups_performed 0
}
# Run the script against the stand-ins with the counters on stdin and the
# entries planted at the modification times given, and print its exit status.
stand_in() {
    local stats=$scratch/stub-stats dir=$scratch/stub-cache planted
    cat > "$stats"
    rm -rf "$dir" "$dir.age"
    mkdir -p "$dir/a/b"
    for planted in "$@"; do touch -m -d "@$planted" "$dir/a/b/entry-$planted"; done
    env PATH="$scratch/stub:$PATH" STUB_STATS="$stats" STUB_DIR="$dir" STUB_NOW="$stub_now" \
        bash "$script" "$stub_start" > "$scratch/stub.log" 2>&1
    echo "$?"
}
rc=$(counters | stand_in)
age=$(cat "$scratch/stub-cache.age" 2> /dev/null)
if [ "$rc" -eq 0 ] && [ "$age" = "101s" ]; then
    report ok "stand-in: a run of 100 s evicts at 101s"
else
    report red "stand-in: a run of 100 s exited $rc and evicted at '$age', not 0 and 101s"
fi
rc=$(counters | stand_in "$((stub_start - 1))")
if [ "$rc" -eq 1 ]; then
    report ok "stand-in: an entry at START - 1 that survives fails the script"
else
    report red "stand-in: an entry at START - 1 that survives exited $rc, not 1"
fi
rc=$(counters | stand_in "$((stub_start - 1)).5")
if [ "$rc" -eq 0 ]; then
    report ok "stand-in: an entry at START - 0.5 that survives does not"
else
    report red "stand-in: an entry at START - 0.5 that survives exited $rc, not 0"
fi
rc=$(counters | grep -v '^preprocessor_error' | stand_in)
if [ "$rc" -eq 1 ]; then
    report ok "stand-in: a counter ccache omits fails the script"
else
    report red "stand-in: a counter ccache omits exited $rc, not 1"
fi
rc=$({ counters; printf 'cache_miss\t0\n'; } | stand_in)
if [ "$rc" -eq 1 ]; then
    report ok "stand-in: a counter ccache reports twice fails the script"
else
    report red "stand-in: a counter ccache reports twice exited $rc, not 1"
fi

for tool in ccache clang++-23; do
    command -v "$tool" > /dev/null || { echo "$tool not installed, the real-ccache part is untestable"; exit "$status"; }
done
[ -x "$HOME/.local/bin/mull-ir-frontend-23" ] || { echo "plugin not installed, the real-ccache part is untestable"; exit "$status"; }
[ -x python/.venv/bin/python ] || { echo "python/.venv missing, the real-ccache part is untestable"; exit "$status"; }

export CCACHE_DIR="$scratch/ccache" CCACHE_MAXSIZE=1G
echo "with $(ccache --version | head -n 1)"

# Build slice NUMBER of the leak tree into DIRECTORY, wiped first, the way a lane builds it.
build() {
    rm -rf "${tree:?}/$2"
    PYTHONPATH=. python/.venv/bin/python - "$1" "$tree/$2" "$scratch" <<'PY' > "$scratch/build.log" 2>&1
import sys
from pathlib import Path

from tools.mutation_cpp import LegPaths, build_cpp_mutation_tree, cpp_sweep_directory
from tools.mutation_cpp_config import leg_config
from tools.mutation_cpp_legs import CppLeg, CppTree

number, build, scratch = sys.argv[1:]
leg = CppLeg(CppTree.LEAK, int(number))
build_dir = Path(build)
artifact = Path(scratch) / f"artifact-{number}"
artifact.mkdir(exist_ok=True)
config = leg_config(leg, build_dir)
built = build_cpp_mutation_tree("cmake", LegPaths(cpp_sweep_directory(), build_dir, artifact, config), leg)
sys.exit(0 if isinstance(built, str) else 1)
PY
}
# Every stored entry, by path, as ccache lists them, and the results among
# them: byte 3 of an entry is its type, 0 for a result and 1 for a manifest.
entries() {
    find "$CCACHE_DIR" -mindepth 3 -type f ! -name stats ! -name '.nfs*' -printf '%P\n' | sort
}
results() {
    local entry
    while read -r entry; do
        [ "$(od -An -tu1 -j3 -N1 "$CCACHE_DIR/$entry" | tr -d ' ')" = 0 ] && echo "$entry"
    done < <(entries)
}
counter() {
    ccache --print-stats | awk -F'\t' -v key="$1" '$1 == key {print $2}'
}
# Age every entry's modification time an hour, zero the counters, take the
# start, set every access time to it or later, and print the start.
begin() {
    local began
    find "$CCACHE_DIR" -mindepth 3 -type f -exec touch -m -d '1 hour ago' {} +
    ccache --zero-stats > /dev/null
    began=$(date +%s)
    find "$CCACHE_DIR" -mindepth 3 -type f -exec touch -a {} +
    echo "$began"
}
# Run the script, and refuse it unless it exits 0 by the branch named: an
# eviction, a run that compiled nothing, or a failed compile.
evict() {
    local expected
    case "$2" in
        evicted) expected='^after eviction:' ;;
        nothing) expected='compiled nothing' ;;
        failed) expected='a compile failed' ;;
    esac
    bash "$script" "$1" > "$scratch/evict.log" 2>&1 || { echo "the script failed:"; cat "$scratch/evict.log"; exit 1; }
    grep -q -- "$expected" "$scratch/evict.log" ||
        { echo "the script did not take the $2 branch:"; cat "$scratch/evict.log"; exit 1; }
}

build 1 first || { echo "slice 1 did not build:"; tail -5 "$scratch/build.log"; exit 1; }
entries > "$scratch/first"
results > "$scratch/first-results"
[ -s "$scratch/first-results" ] || { echo "the first build stored no result"; exit 1; }

printf 'int unread() { return 0; }\n' > "$scratch/unread.cpp"
ccache clang++-23 -c "$scratch/unread.cpp" -o "$scratch/unread.o" > /dev/null 2>&1
entries > "$scratch/with-unread"
comm -13 "$scratch/first" "$scratch/with-unread" > "$scratch/unread"
[ -s "$scratch/unread" ] || { echo "the unread unit stored no entry"; exit 1; }
began=$(begin)
build 1 first || { echo "slice 1 did not rebuild:"; tail -5 "$scratch/build.log"; exit 1; }
if [ "$(counter cache_miss)" -ne 0 ] || [ "$(counter preprocessed_cache_hit)" -ne 0 ]; then
    echo "the direct rebuild missed or hit in preprocessor mode, so it is no all-direct case"
    exit 1
fi
evict "$began" evicted
entries > "$scratch/after"
if cmp -s "$scratch/first" "$scratch/after"; then
    report ok "direct rebuild: $(wc -l < "$scratch/first") entries kept, the $(wc -l < "$scratch/unread") it did not read gone"
else
    report red "direct rebuild: $(comm -23 "$scratch/first" "$scratch/after" | wc -l) entries it read evicted, $(comm -13 "$scratch/first" "$scratch/after" | wc -l) it did not read kept"
fi

began=$(begin)
CCACHE_NODIRECT=1 build 1 first || { echo "slice 1 did not rebuild in preprocessor mode:"; tail -5 "$scratch/build.log"; exit 1; }
if [ "$(counter cache_miss)" -ne 0 ] || [ "$(counter direct_cache_hit)" -ne 0 ]; then
    echo "the preprocessor-mode rebuild missed or hit directly, so it is no all-preprocessed case"
    exit 1
fi
evict "$began" evicted
results > "$scratch/after-results"
entries > "$scratch/after"
if ! cmp -s "$scratch/first-results" "$scratch/after-results"; then
    report red "preprocessor-mode rebuild: $(comm -23 "$scratch/first-results" "$scratch/after-results" | wc -l) results the build read were evicted"
elif ! cmp -s "$scratch/after-results" "$scratch/after"; then
    report red "preprocessor-mode rebuild: $(comm -23 "$scratch/after" "$scratch/after-results" | wc -l) manifests it did not read were kept"
else
    report ok "preprocessor-mode rebuild: $(wc -l < "$scratch/first-results") results kept, every manifest gone"
fi
entries > "$scratch/first"

began=$(begin)
build 2 other || { echo "slice 2 did not build:"; tail -5 "$scratch/build.log"; exit 1; }
hits=$(($(counter direct_cache_hit) + $(counter preprocessed_cache_hit)))
[ "$hits" -eq 0 ] || { echo "slice 2 hit $hits of slice 1's objects, so it is no all-miss case"; exit 1; }
entries > "$scratch/before"
comm -13 "$scratch/first" "$scratch/before" > "$scratch/own"
[ -s "$scratch/own" ] || { echo "slice 2 stored no entry"; exit 1; }
evict "$began" evicted
entries > "$scratch/after"
kept_first=$(comm -12 "$scratch/first" "$scratch/after" | wc -l)
if [ "$kept_first" -eq 0 ] && cmp -s "$scratch/own" "$scratch/after"; then
    report ok "other slice: $(wc -l < "$scratch/own") entries of its own kept, none of the first's $(wc -l < "$scratch/first")"
else
    report red "other slice: $kept_first of the first build's entries kept, $(comm -23 "$scratch/own" "$scratch/after" | wc -l) of its own evicted"
fi

began=$(begin)
entries > "$scratch/before"
evict "$began" nothing
entries > "$scratch/after"
if cmp -s "$scratch/before" "$scratch/after"; then
    report ok "nothing compiled: $(wc -l < "$scratch/before") entries, every one kept"
else
    report red "nothing compiled: $(comm -23 "$scratch/before" "$scratch/after" | wc -l) entries evicted"
fi

printf 'int broken(\n' > "$scratch/broken.cpp"
printf '#include "absent.hpp"\n' > "$scratch/unpreprocessed.cpp"
# One good unit, so the run is one that compiled, beside one that fails as
# COUNTER names, the cache's entries aged first; every entry must stay.
failing_arm() {
    local name=$1 unit=$2 counted=$3
    began=$(begin)
    printf 'int %s() { return 0; }\n' "$counted" > "$scratch/fine-$counted.cpp"
    ccache clang++-23 -c "$scratch/fine-$counted.cpp" -o "$scratch/fine.o" > /dev/null 2>&1
    ccache clang++-23 -c "$scratch/$unit" -o "$scratch/failed.o" > /dev/null 2>&1
    if [ "$(counter cache_miss)" -ne 1 ] || [ "$(counter "$counted")" -ne 1 ] ||
        [ "$(($(counter compile_failed) + $(counter preprocessor_error)))" -ne 1 ]; then
        echo "the two units of the $name arm are not one miss and one $counted alone"
        exit 1
    fi
    entries > "$scratch/before"
    evict "$began" failed
    entries > "$scratch/after"
    if cmp -s "$scratch/before" "$scratch/after"; then
        report ok "$name: $(wc -l < "$scratch/before") entries, every one kept"
    else
        report red "$name: $(comm -23 "$scratch/before" "$scratch/after" | wc -l) entries evicted"
    fi
}
failing_arm "failed compile" broken.cpp compile_failed
failing_arm "preprocessor error" unpreprocessed.cpp preprocessor_error
exit "$status"
