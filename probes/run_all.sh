# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Runs every probe in this directory from the repository root and prints one
# line per probe: PASS or FAIL, then the probe's path. Exits non-zero when any
# probe fails. A probe is a bash script named <subject>--<property>.sh that
# exits zero when the property it states in its header holds.
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 2
status=0
count=0
for probe in $(find probes -name '*.sh' ! -name run_all.sh | sort); do
    count=$((count + 1))
    if bash "$probe" > /dev/null 2>&1; then
        echo "PASS $probe"
    else
        echo "FAIL $probe"
        status=1
    fi
done
echo "probes: $count run, exit $status"
exit $status
