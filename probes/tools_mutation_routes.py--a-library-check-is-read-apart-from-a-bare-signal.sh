#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes tools/mutation_routes.py.
# Claim: the route reader tells a run the standard library's own check ended,
# debug mode's message or an assertion's, from one a bare signal ended, and a
# test's own assertion still comes before either. Each route is fed the shape
# of output a real sweep captured for it: the debug-mode report a past-the-end
# read prints, an assertion's line, the sanitizer runtime's report of a
# signal, LeakSanitizer's leak report, the kernel's own error line, and a
# Catch2 block for a failed assertion beside a Catch2 block for a fatal signal.
# Non-zero exit: any sample reads a route other than the one it stands for, or
# the check route is missing from the order kills are attributed in.
set -u
cd "$(dirname "$0")/.." || exit 2
py=python/.venv/bin/python
[ -x "$py" ] || exit 2
"$py" - <<'PY'
import sys
from tools.mutation_routes import KILL_ROUTES, MULL_PASSED, MULL_TIMEDOUT, kill_route

FAILED = "/x/excel_tests.cpp:1176: FAILED:\n  CHECK_THAT( message, ContainsSubstring(\"missing\") )\nwith expansion:\n  \"std::bad_alloc\" contains: \"missing\"\n\n"
FATAL = "/x/excel_tests.cpp:1170: FAILED:\n  {Unknown expression after the reported line}\ndue to a fatal error condition:\n  SIGSEGV - Segmentation violation signal\n\n"
DEBUG = "/usr/include/c++/16/debug/safe_iterator.h:372:\nIn function:\n    pointer operator->() const\n\nError: attempt to dereference a past-the-end iterator.\n\nObjects involved in the operation:\n"
ASSERT = "/usr/include/c++/16/bits/stl_vector.h:1272: reference std::vector<int>::operator[](size_type): Assertion '__n < this->size()' failed.\n"
SIGNAL = "LeakSanitizer:DEADLYSIGNAL\n==1==ERROR: LeakSanitizer: SEGV on unknown address 0x000000000000 (pc 0x1 bp 0x2 sp 0x3 T0)\n"
LEAK = "\n=================================================================\n==1==ERROR: LeakSanitizer: detected memory leaks\n"
KERNEL = "aletheia: kernel refused the frame\n"
cases = [
    ("a test's assertion", 1, FAILED, "", "test"),
    ("a test's assertion, then a library check on the way down", 1, FAILED + FATAL, DEBUG, "test"),
    ("debug mode's past-the-end report", 1, FATAL, DEBUG, "check"),
    ("an assertion the library checks", 1, FATAL, ASSERT, "check"),
    ("a bare signal inside a test case", 1, FATAL, SIGNAL, "fault"),
    ("a bare signal outside any test case", 1, "", SIGNAL, "fault"),
    ("a leak", 1, "", LEAK, "leak"),
    ("the kernel's own error path", 1, "", KERNEL, "kernel"),
    ("every test passed", MULL_PASSED, "All tests passed\n", "", "survived"),
    ("the runner ended it", MULL_TIMEDOUT, "", "", "timeout"),
]
bad = [f"{name}: read {kill_route(status, out, err)}, stands for {want}"
       for name, status, out, err, want in cases if kill_route(status, out, err) != want]
if "check" not in KILL_ROUTES or KILL_ROUTES.index("test") > KILL_ROUTES.index("check"):
    bad.append(f"attribution order {KILL_ROUTES} lacks check after test")
for line in bad:
    print(line)
print(f"{len(cases)} samples, {len(cases) - len(bad)} read as they stand for")
sys.exit(1 if bad else 0)
PY
