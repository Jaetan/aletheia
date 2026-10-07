#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Runs every probe in this directory from the repository root. A passing probe
# prints one line, PASS and its path, whatever it said. A failing probe prints
# FAIL, its path and its exit status, then the last lines of its own output
# indented beneath, and the whole output is kept in tools/ci-output/probes/,
# in a file the FAIL line names, so a probe that crashed reads differently
# from one that refused its claim. Every line carries the probe's wall time
# after its path, and the run's times are kept in timings.tsv beside the
# failures, one row per probe with its verdict, in the order the probes ran.
# The directory holds only the failures and the times of the latest run.
# Every tracked file's mtime, size and mode are read before
# and after each probe, and a probe that moved one fails whatever it exited,
# its line naming the count and its log the paths: a write the probe restores
# still reads as the user's change to a sweep, a hook or a commit meanwhile,
# and this is the check the store's own probe cannot make on a computed path.
# Exits non-zero when any probe fails, and 2 where the tracked files cannot be
# listed or the shell cannot read its clock to the microsecond. A probe is a bash script named <subject>--<property>.sh that exits
# zero when the property it states in its header holds. Each one names its
# own interpreter and is executable, so it runs the same whether this runner
# invokes it or a reader does.
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 2
logs=tools/ci-output/probes
timings=$logs/timings.tsv
shown=12
[ -n "${EPOCHREALTIME:-}" ] || { echo "run_all: this shell has no EPOCHREALTIME (bash 5), so a probe's time cannot be read"; exit 2; }
mkdir -p "$logs" || exit 2
rm -f "$logs"/*.log
printf 'probe\tverdict\tseconds\n' > "$timings" || exit 2
# Microseconds since the epoch, whatever separator the locale puts in the clock.
now() { echo "${EPOCHREALTIME//[^0-9]/}"; }
tracked() { git ls-files -z | xargs -0 stat -c '%n %.9Y %s %a' 2> /dev/null; }
git ls-files > /dev/null || { echo "run_all: not in a git work tree, so a write to a tracked file cannot be seen"; exit 2; }
status=0
count=0
for probe in $(find probes -name '*.sh' ! -name run_all.sh | sort); do
    count=$((count + 1))
    log="$logs/$(basename "$probe" .sh).log"
    tracked > "$logs/tracked.before"
    start=$(now)
    bash "$probe" > "$log" 2>&1
    rc=$?
    end=$(now)
    tracked > "$logs/tracked.after"
    took=$(((end - start) / 1000000)).$(((end - start) / 100000 % 10))
    moved=$(diff "$logs/tracked.before" "$logs/tracked.after" | sed -n 's/^[<>] \(.*\) [0-9.]* [0-9]* [0-9]*$/\1/p' | sort -u)
    if [ -n "$moved" ]; then
        {
            echo "the probe moved these tracked files, whatever it wrote back:"
            echo "$moved"
        } >> "$log"
        lines=$(grep -c '' "$log")
        echo "FAIL $probe ${took}s exit $rc, moved $(echo "$moved" | grep -c '') tracked file(s), $lines lines kept in $log"
        tail -n "$shown" "$log" | sed 's/^/    /'
        status=1
        verdict=FAIL
    elif [ "$rc" -eq 0 ]; then
        echo "PASS $probe ${took}s"
        rm -f "$log"
        verdict=PASS
    else
        lines=$(grep -c '' "$log")
        echo "FAIL $probe ${took}s exit $rc, $lines lines kept in $log"
        tail -n "$shown" "$log" | sed 's/^/    /'
        status=1
        verdict=FAIL
    fi
    printf '%s\t%s\t%s\n' "$probe" "$verdict" "$took" >> "$timings"
done
rm -f "$logs/tracked.before" "$logs/tracked.after"
echo "probes: $count run, exit $status"
exit $status
