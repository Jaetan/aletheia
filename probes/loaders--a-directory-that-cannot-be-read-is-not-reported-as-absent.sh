#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/excel/hardening.go, cpp/src/detail/loader_utils.cpp and
# python/aletheia/excel_loader.py.
# Claim: before a template is written, a parent directory that cannot be looked
# at is not reported as one that is not there. The two are different repairs: a
# reader told a directory is absent creates it, and a reader told the stat
# failed looks at permissions, at the path's length, or at what else the
# machine is doing. A component longer than a name may be is the trigger,
# because it needs no permissions and no root.
# Python is exercised directly, having no such check of its own and getting the
# distinction from the operating system. Go and C++ are exercised through the
# two test cases each carries, which is what they offer without a build of a
# throwaway program inside the tree; a case renamed or deleted fails here, and
# remembering those names is half of what this probe is for.
# Non-zero exit: a binding answers a stat failure with the words for absence.
# Exits 2 without Go, without the venv, or without a configured C++ tree.
set -u
cd "$(dirname "$0")/.." || exit 2
command -v go > /dev/null || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2

work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT
long=$(printf 'a%.0s' $(seq 1 5000))

# --- Python -----------------------------------------------------------------
py_out=$("$py" - "$work/absent" "/tmp/$long" <<'PY'
import sys
from pathlib import Path

from aletheia.excel_loader import create_template

for parent in sys.argv[1:]:
    try:
        create_template(Path(parent) / "template.xlsx")
        print("no refusal")
    except OSError as exc:
        print(f"{type(exc).__name__}: errno {exc.errno}")
PY
) || { echo "the Python surface could not be run"; exit 2; }
py_absent=$(printf '%s\n' "$py_out" | sed -n 1p)
py_stat=$(printf '%s\n' "$py_out" | sed -n 2p)

bad=0
case "$py_absent" in
    "FileNotFoundError: errno 2") ;;
    *) echo "Python, an absent parent: $py_absent"; bad=1 ;;
esac
case "$py_stat" in
    "FileNotFoundError: errno 2") echo "Python answers a stat failure as absence: $py_stat"; bad=1 ;;
    "OSError: errno "*) ;;
    *) echo "Python, a parent it cannot stat: $py_stat"; bad=1 ;;
esac

# --- Go, through its own two cases ------------------------------------------
for case_name in TestCreateTemplate_RejectsMissingParentDir \
                 TestCreateTemplate_StatFailureNotMislabeled; do
    if ! (cd go/excel && go test ./... -count=1 -run "^${case_name}\$") > /dev/null 2>&1; then
        echo "the Go case did not pass: $case_name"
        bad=1
    fi
done

# --- C++, through its own two cases -----------------------------------------
if [ -f cpp/build/CMakeCache.txt ]; then
    if cmake --build cpp/build --target excel_tests > /dev/null 2>&1; then
        for case_name in "excel: create_template parent dir missing rejected" \
                         "excel: create_template stat failure is distinguished from a missing parent"; do
            if ! ALETHEIA_LIB=$PWD/build/libaletheia-ffi.so ./cpp/build/excel_tests "$case_name" \
                > /dev/null 2>&1; then
                echo "the C++ case did not pass: $case_name"
                bad=1
            fi
        done
    else
        echo "the C++ tests did not build"
        bad=1
    fi
fi

[ "$bad" -eq 0 ] || exit 1
echo "PASS: a parent that cannot be stat'd is refused differently from one that is absent"
