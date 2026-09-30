#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes examples/demo/drive_log.py, its main block.
# Claim: a plain run checks drive.log against the generators and writes
# nothing: it exits 0 on the tracked drive.log and 1 on one with a byte
# appended, leaving the file as found both times. The run is over copies of
# the two files in a scratch directory, the copied log's mtime set in the past,
# so a rewrite of the same bytes still reads as a moved mtime.
# Non-zero exit: a plain run rewrote drive.log, read the tracked one as drift,
# or read a drifted one as a match. Exit 2 without the venv.
set -u
cd "$(dirname "$0")/.." || exit 2
py="$PWD/python/.venv/bin/python"
[ -x "$py" ] || exit 2
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
cp examples/demo/drive_log.py examples/demo/drive.log "$work/" || exit 2
check() { # $1: the exit status a plain run owes, $2: which log it reads
	touch -d '2000-01-01 00:00:00' "$work/drive.log" || exit 2
	before=$(stat -c '%Y %s' "$work/drive.log")
	(cd "$work" && PYTHONDONTWRITEBYTECODE=1 "$py" drive_log.py) > "$work/out.txt" 2>&1
	rc=$?
	[ "$rc" -eq "$1" ] || { echo "a plain run exited $rc on $2, not $1:"; tail -3 "$work/out.txt"; exit 1; }
	[ "$(stat -c '%Y %s' "$work/drive.log")" = "$before" ] || { echo "a plain run rewrote $2"; exit 1; }
}
check 0 "the tracked drive.log"
printf 'x' >> "$work/drive.log"
check 1 "a drifted drive.log"
echo "PASS: a plain run checks drive.log and writes nothing"
