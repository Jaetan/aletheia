#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes README.md, its exit-code list under the 60-second try.
# Claim: `aletheia check` exits 0 when it finds no violation, a check whose
# signal never appeared included: the README says such a check is reported
# unresolved and also exits 0. The demo checks are run over a one-frame log
# whose frame carries an identifier the demo DBC does not define, so every
# check stays unresolved. The library is build/libaletheia-ffi.so, or the path
# ALETHEIA_LIB names, which the Python loader reads too.
# Non-zero exit: the run did not exit 0, or did not report the checks as
# unresolved, or the README no longer says so. Exit 2 without a built library.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
lib=${ALETHEIA_LIB:-build/libaletheia-ffi.so}
[ -f "$lib" ] || { echo "no built library at $lib; build first or set ALETHEIA_LIB"; exit 2; }
grep -qE '^\- \*\*exit 0\*\*.*unresolved.*exits 0' README.md || { echo "README.md no longer says an unresolved check exits 0"; exit 1; }
tmp=$(mktemp -d) || exit 2
trap 'rm -rf "$tmp"' EXIT
printf '(0.000000) can0 7FF#00\n' > "$tmp/one.log"
out=$(cd examples/demo && ALETHEIA_LIB=$(realpath "$lib") PYTHONPATH=../../python \
    "../../$py" -m aletheia check --dbc vehicle.dbc --checks vehicle_checks.yaml "$tmp/one.log" 2>&1)
rc=$?
[ "$rc" -eq 0 ] || { echo "aletheia check exited $rc on a log with no violation:"; printf '%s\n' "$out" | tail -5; exit 1; }
printf '%s\n' "$out" | grep -q 'unresolved' || { echo "the run exited 0 but reported no unresolved check:"; printf '%s\n' "$out" | tail -5; exit 1; }
echo "PASS: no violation, checks unresolved, exit 0"
