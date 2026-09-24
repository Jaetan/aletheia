#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes README.md, the Excel line of the 60-second try.
# Claim: the command the README shows for the code-free spreadsheet path,
# `aletheia check --excel workbook.xlsx trace.log`, is the CLI's shape, and the
# workbook the README names as the filled-in template,
# examples/demo/demo_workbook.xlsx, loads through --excel and runs its checks
# to a verdict over the demo log: exit 0 or 1 with a check summary, never the
# error exit 2. The workbook's DBC is not the demo log's, so its checks come
# out unresolved; the README does not pair the two, which is why the line
# shows placeholders. Bash fences are not run by the doc harness, so this is
# the line's only guard. The library is build/libaletheia-ffi.so, or the path
# ALETHEIA_LIB names.
# Non-zero exit: the README no longer shows the line or the template, or the
# command exits 2 or prints no summary. Exit 2 without a built library.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
lib=${ALETHEIA_LIB:-build/libaletheia-ffi.so}
[ -f "$lib" ] || { echo "no built library at $lib; build first or set ALETHEIA_LIB"; exit 2; }
line=$(grep -oE '^aletheia check --excel [^ ]+ [^ ]+$' README.md)
[ "$line" = "aletheia check --excel workbook.xlsx trace.log" ] || { echo "README.md shows no such Excel line (found: '$line')"; exit 1; }
grep -q 'examples/demo/demo_workbook.xlsx' README.md || { echo "README.md no longer names the template workbook"; exit 1; }
[ -f examples/demo/demo_workbook.xlsx ] || { echo "the template workbook is not in the tree"; exit 1; }
out=$(cd examples/demo && ALETHEIA_LIB=$(realpath "$lib") PYTHONPATH=../../python "../../$py" -m aletheia check --excel demo_workbook.xlsx drive.log 2>&1)
rc=$?
[ "$rc" -eq 0 ] || [ "$rc" -eq 1 ] || { echo "the Excel run exited $rc, not a verdict:"; printf '%s\n' "$out" | tail -5; exit 1; }
printf '%s\n' "$out" | grep -qE '^Summary: [0-9]+ violations, [0-9]+ unresolved in [0-9]+ checks' || { echo "the run exited $rc but printed no check summary:"; printf '%s\n' "$out" | tail -5; exit 1; }
echo "PASS: the template workbook loads through --excel and its checks run to a verdict (exit $rc)"
