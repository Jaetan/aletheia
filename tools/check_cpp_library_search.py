# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Hold the C++ binding to one search for ``libaletheia-ffi.so``.

The renderer that formats values and the backend that answers queries must
load one build, so the binding searches once, in ``find_ffi_library``
(``cpp/src/rational_renderer.cpp``), and every program that looks for the
library calls it: the command-line tool, the throughput benchmark and the
stability benchmark.  Two arms:

* a path literal naming the library, a string literal holding no whitespace
  (so not a message that mentions the name), is a candidate of its own,
  refused in every tracked C++ source of the binding but the search's; the
  tests are not read, since each names the one build the suite runs on;
* a caller whose code, its ``//`` comments aside, no longer calls
  ``find_ffi_library`` is refused, and so is a caller that is not tracked.

Run ``python -m tools.check_cpp_library_search`` from the repository root.
Exit 0 = clean, 1 = a finding, 2 = could-not-check (a tracked file was
unreadable, never reported as clean).  Unit-tested by
``python/tests/test_check_cpp_library_search.py``.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from tools._common import RelPath, TreeScan, git_ls_files, report_tree_scan
from tools._hosted_markdown import SourceText, scan_tracked_sources

from aletheia.common_types import ExitStatus, Prose

REPO_ROOT = Path(__file__).resolve().parent.parent

SEARCH = RelPath("cpp/src/rational_renderer.cpp")
CALLERS = (
    RelPath("cpp/src/cli/cli.cpp"),
    RelPath("cpp/benchmarks/benchmark.cpp"),
    RelPath("cpp/benchmarks/stability_bench.cpp"),
)

_CPP_SUFFIXES = (".cpp", ".hpp", ".h")
_PATH_LITERAL = re.compile(r'"[^"\s]*libaletheia-ffi\.so"')
_SEARCH_CALL = re.compile(r"\bfind_ffi_library\(")


def scan_file(rel: RelPath, text: SourceText) -> list[Prose]:
    """Return every finding of the tracked C++ source ``rel``."""
    lines = text.splitlines()
    findings = [
        Prose(
            f"{rel}:{number}: a library candidate of its own, where the binding searches once"
            + f" in {SEARCH}: {match.group(0)}"
        )
        for number, line in enumerate(lines, start=1)
        for match in _PATH_LITERAL.finditer(line)
        if rel != SEARCH
    ]
    if rel in CALLERS and not any(_SEARCH_CALL.search(line.partition("//")[0]) for line in lines):
        findings.append(Prose(f"{rel}: does not call find_ffi_library, the binding's one search"))
    return findings


def _is_not_read(rel: RelPath) -> bool:
    """Whether the tracked file ``rel`` is one the gate does not read."""
    return (
        not rel.startswith("cpp/")
        or rel.startswith("cpp/tests/")
        or not rel.endswith(_CPP_SUFFIXES)
    )


def main() -> ExitStatus:
    """Report every candidate outside the search and every caller not calling it."""
    argparse.ArgumentParser(description=__doc__).parse_args()  # no options; --help only
    scan = scan_tracked_sources(REPO_ROOT, _is_not_read, scan_file)
    tracked = set(git_ls_files(REPO_ROOT))
    untracked = [
        f"{caller}: a caller the gate holds is not tracked"
        for caller in CALLERS
        if caller not in tracked
    ]
    scan = TreeScan([*scan.findings, *untracked], scan.unreadable)
    return ExitStatus(
        report_tree_scan(
            "check_cpp_library_search",
            scan,
            found=f"{len(scan.findings)} departure(s) from the binding's one library search:",
            found_lines=scan.findings,
            clean="one search for libaletheia-ffi.so, and every caller calls it.",
        )
    )


if __name__ == "__main__":
    sys.exit(main())
