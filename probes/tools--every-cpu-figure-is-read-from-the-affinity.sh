#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes the tracked Python under tools/ and the tracked shell under tools/
# and probes/; a scratch checkout left under tools/ci-output/ is not read.
# Claim: no job count or pinned CPU list there is counted from the machine.
# os.cpu_count and multiprocessing.cpu_count count every CPU the machine has
# whatever the process was given, and a taskset list counted up from zero
# names CPUs the process may not have been given, which taskset -c then
# widens onto. The count is os.process_cpu_count through detect_cpus in
# tools/_resources.py, and the list is polite_cpu_list beside it.
# Non-zero exit: a line calls or imports either cpu_count, or builds a taskset
# range from 0 by arithmetic; each is printed.
set -u
cd "$(dirname "$0")/.." || exit 2
git ls-files --error-unmatch tools probes > /dev/null 2>&1 || exit 2

# git grep exits 1 on no match and higher on an error, which must not read as
# a pass.
counted=$(git grep -nP '(?<!process_)\bcpu_count\s*\(|\bimport\b.*\bcpu_count\b' -- 'tools/*.py')
[ $? -le 1 ] || exit 2
ranged=$(git grep -nP '0-\$\(\(' -- 'tools/*.sh' 'probes/*.sh' ":(exclude)probes/$(basename "$0")")
[ $? -le 1 ] || exit 2
found=$(printf '%s\n%s\n' "$counted" "$ranged" | grep .)
if [ -n "$found" ]; then
	echo "counted from the machine rather than from the CPUs the process was given:"
	echo "$found" | sed 's/^/  /'
	exit 1
fi
echo "PASS: every CPU figure under tools/ and probes/ is read from the affinity"
