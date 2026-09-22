#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Runs every probe in this directory from the repository root. A passing probe
# prints one line, PASS and its path, whatever it said. A failing probe prints
# FAIL, its path and its exit status, then the last lines of its own output
# indented beneath, and the whole output is kept in tools/ci-output/probes/,
# in a file the FAIL line names, so a probe that crashed reads differently
# from one that refused its claim. The directory holds only the failures of
# the latest run. Exits non-zero when any probe fails. A probe is a bash
# script named <subject>--<property>.sh that exits zero when the property it
# states in its header holds. Each one names its own interpreter and is
# executable, so it runs the same whether this runner invokes it or a reader
# does.
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 2
logs=tools/ci-output/probes
shown=12
mkdir -p "$logs" || exit 2
rm -f "$logs"/*.log
status=0
count=0
for probe in $(find probes -name '*.sh' ! -name run_all.sh | sort); do
    count=$((count + 1))
    log="$logs/$(basename "$probe" .sh).log"
    bash "$probe" > "$log" 2>&1
    rc=$?
    if [ "$rc" -eq 0 ]; then
        echo "PASS $probe"
        rm -f "$log"
    else
        lines=$(grep -c '' "$log")
        echo "FAIL $probe exit $rc, $lines lines kept in $log"
        tail -n "$shown" "$log" | sed 's/^/    /'
        status=1
    fi
done
echo "probes: $count run, exit $status"
exit $status
