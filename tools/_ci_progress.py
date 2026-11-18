# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""How each step of the sweep reports its progress, and how long it may go without a report.

Every step reports its progress in its own output (``tools._watchdog``): a
line its pattern matches, naming how much of its work is done where the tool
says.  A tool that counts its work prints its own count: pytest's percentage,
ctest's and clang-tidy's ``k/n``, cabal's ``[k of n]``, CMake's percentage,
go test's and cargo's line per package, test or crate.  A tool of ours reports
through ``tools._progress``.  A third-party tool that prints no count reports
nothing, and its allowance holds it from its start.  The table names each
step as ``tools/_ci_steps.py`` registers it; a step it does not name reports
nothing and holds no deadline.
"""

from __future__ import annotations

import re
from dataclasses import replace
from typing import TYPE_CHECKING

from tools._common import GateName
from tools._progress import REPORT
from tools._watchdog import NO_REPORTS_YET, PatternText, Progress, Seconds

if TYPE_CHECKING:
    from collections.abc import Mapping

# The lines each kind of tool's own count is printed on, as the watchdog reads them: stripped.
_OURS = Progress(PatternText(REPORT))
_PYTEST = Progress(PatternText(r"\[\s*(?P<percent>\d+)%\]$"))
_CTEST = Progress(PatternText(r"^(?P<done>\d+)/(?P<total>\d+) Test\s+#|^\[\s*(?P<percent>\d+)%\]"))
_CMAKE_BUILD = Progress(PatternText(r"^\[\s*(?P<percent>\d+)%\]"))
_CLANG_TIDY = Progress(PatternText(r"^\[\s*(?P<done>\d+)/(?P<total>\d+)\]\["))
_AGDA_GATES = Progress(PatternText(r"^\[\s*(?P<done>\d+)/(?P<total>\d+)\]|^# \S+ \(for "))
_SHAKE_BUILD = Progress(PatternText(r"^\[\s*(?P<done>\d+) of (?P<total>\d+)\]|^# \S+ \(for "))
_GO_TEST = Progress(PatternText(r"^(ok|FAIL|---|\?)\s"))
_CARGO_TEST = Progress(PatternText(r"^test .+ \.\.\. (ok|FAILED|ignored)$|^running \d+ tests?$"))
_CARGO_BUILD = Progress(PatternText(r"^(Compiling|Checking|Documenting|Finished|Fresh)\s"))
# A third-party tool that prints no count: it reports nothing.
_SILENT = NO_REPORTS_YET


def _either(*kinds: Progress) -> Progress:
    """Join kinds of report into one pattern, each kind's count groups given a suffix of its own."""
    parts = [
        re.sub(r"\(\?P<(done|total|percent)>", rf"(?P<\1_{place}>", kind.pattern)
        for place, kind in enumerate(kinds)
    ]
    return Progress(PatternText("|".join(f"(?:{part})" for part in parts)))


# The mutation tools' own counts: mutmut's and Mull's ``k/n``, gremlins' and cargo-mutants' outcome
# of each mutant as it is tested, and cargo-mutants' run of the unmutated tree before them.
_MUTATION_TOOLS = Progress(
    PatternText(
        r"(?P<done>\d+)/(?P<total>\d+)(?:\s+🎉|\. )"
        + r"|^\s*(KILLED|LIVED|NOT COVERED|TIMED OUT|NOT VIABLE)\s"
        + r"|^(caught|MISSED|TIMEOUT|unviable)\s+\S|^ok\s+Unmutated baseline\b"
    )
)
_MUTATION = _either(_OURS, _MUTATION_TOOLS)

_DECLARED = {
    "build": _SHAKE_BUILD,
    "build staleness": _OURS,
    "agda gates": _AGDA_GATES,
    "iwyu": _OURS,
    "iwyu-self-test": _OURS,
    "pytest": _PYTEST,
    "check-bench-schema": _OURS,
    "pytest --markdown-docs": _PYTEST,
    "pytest -X dev": _PYTEST,
    "pytest --random-order": _PYTEST,
    "go test -race": _GO_TEST,
    "cpp configure": _SILENT,
    "check-limits-parity": _OURS,
    "cpp build": _CMAKE_BUILD,
    "ctest": _CTEST,
    "pytest (cli parity)": _PYTEST,
    "pytest (C++ compile database)": _PYTEST,
    "check-cpp-installed-consumer": _OURS,
    "cargo build (tests)": _CARGO_BUILD,
    "cargo test": _CARGO_TEST,
    "cargo build (tests, excel crate)": _CARGO_BUILD,
    "cargo test (excel crate)": _CARGO_TEST,
    "check-rust-licences": _OURS,
    "ruff": _SILENT,
    "ruff format": _SILENT,
    "basedpyright": _SILENT,
    "pylint": _SILENT,
    "gofmt": _SILENT,
    "go vet": _SILENT,
    "go build (no cgo)": _SILENT,
    "go test (no cgo)": _GO_TEST,
    "clang-format": _SILENT,
    "cmake-lint": _SILENT,
    "clang-tidy configure": _SILENT,
    "clang-tidy": _CLANG_TIDY,
    "check-coverage-setup": _OURS,
    "check-clang-tidy-coverage": _OURS,
    "check-cpp-ast": _OURS,
    "check-cpp-const-locals": _OURS,
    "cargo fmt": _SILENT,
    "cargo clippy": _CARGO_BUILD,
    "cargo doc (warnings = errors)": _CARGO_BUILD,
    "cargo fmt (excel crate)": _SILENT,
    "cargo clippy (excel crate)": _CARGO_BUILD,
    "cargo doc (excel crate, warnings = errors)": _CARGO_BUILD,
    "check-action-pins": _OURS,
    "check-workflow-permissions": _OURS,
    "check-spdx-headers": _OURS,
    "check-source-length": _OURS,
    "check-docs": _OURS,
    "check-no-review-marks": _OURS,
    "check-refused-words": _OURS,
    "check-fence-marks": _OURS,
    "check-cpp-fence-const-auto": _OURS,
    "check-cpp-library-search": _OURS,
    "check-no-memory-citations": _OURS,
    "check-venv-convention": _OURS,
    "check-cpp-index-loops": _OURS,
    "check-cpp-layout": _OURS,
    "check-precise-hints": _OURS,
    "check-test-determinism": _OURS,
    "check-runtime-closure": _OURS,
    "check-wire-codes": _OURS,
    "check-gates-reached": _OURS,
    "check-shim-builds-no-kernel-value": _OURS,
    "check-rts-runtime": _OURS,
    "check-sbom-coverage": _OURS,
    "check-install-freshness": _OURS,
    "check-dist-staging": _OURS,
    "check-python-wheel": _OURS,
    "check-clang-format-config": _OURS,
    "check-agda-interface-reuse": _OURS,
    "check-clang-tidy-facts": _OURS,
    "check-json-cleanup-abort": _OURS,
    "ubsan ctest": _CTEST,
    "asan ctest": _CTEST,
    "check-reproducible-build": _OURS,
    "stability bench": _OURS,
    "mutation testing": _MUTATION,
    "coverage python": _either(_OURS, _PYTEST),
    "coverage go": _either(_OURS, _GO_TEST),
    "coverage cpp": _either(_OURS, _CTEST),
    "coverage rust": _either(_OURS, _CARGO_TEST),
    "check-cargo-mutants-shards": _OURS,
    "check-mutmut-operators": _OURS,
    "check-mutmut-witness": _OURS,
    "check-mull-plugin-facts": _OURS,
    "check-cpp-slices-census-build": _OURS,
    "check-cpp-slices-census": _OURS,
    "actionlint": _SILENT,
}

# How long a step may go without a report before the watchdog stops it and fails it: five times
# the longest stretch measured without one, and never less than the floor, so a step is stopped
# for being stuck and never for running on a slower machine.
ALLOWANCE_FLOOR = Seconds(15 * 60.0)
_ALLOWANCE_FACTOR = 5.0
# The longest stretch measured without a report, for each step five times which passes the floor.
# Measured on this tree's sweeps, warm and cold, every lane on, and on GitHub's runners.
LONGEST_QUIET: Mapping[GateName, Seconds] = {
    GateName("build"): Seconds(238.0),  # a cold build of the kernel on GitHub's runners
    # Its longer clean build on GitHub's runners, which prints nothing while it runs.
    GateName("check-reproducible-build"): Seconds(334.0),
}


def allowance_for(quiet: Seconds) -> Seconds:
    """Return the allowance of a step whose longest stretch without a report is ``quiet``."""
    return Seconds(max(ALLOWANCE_FLOOR, _ALLOWANCE_FACTOR * quiet))


STEP_PROGRESS: Mapping[GateName, Progress] = {
    GateName(name): replace(
        progress, allowance=allowance_for(LONGEST_QUIET.get(GateName(name), Seconds(0.0)))
    )
    for name, progress in _DECLARED.items()
}
# The longest allowance any step of the sweep has.
LONGEST_STEP_ALLOWANCE = Seconds(
    max(p.allowance or ALLOWANCE_FLOOR for p in STEP_PROGRESS.values())
)


def progress_of(name: GateName) -> Progress:
    """Return how step ``name`` reports its progress, or no reports when the table names it not."""
    return STEP_PROGRESS.get(name, NO_REPORTS_YET)


# Coverage of every binding in one run: each binding's test runner counts as it runs, and the run
# goes no longer without a report than the slowest binding's own step may.
COVERAGE_OF_EVERY_BINDING = replace(
    _either(_OURS, _PYTEST, _GO_TEST, _CTEST, _CARGO_TEST),
    allowance=max(
        STEP_PROGRESS[GateName(f"coverage {binding}")].allowance or ALLOWANCE_FLOOR
        for binding in ("python", "go", "cpp", "rust")
    ),
)
