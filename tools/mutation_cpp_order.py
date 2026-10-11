# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The order the C++ mutation binary runs its tests in, and the rule its tail is held to.

The lane runs the binary once per mutant under ``--order decl``, so the tests
run in the order their units were linked (cpp/CMakeLists.txt), and under
``--abort``, so a run ends at its first failing assertion.  A mutant therefore
costs every test ahead of the one that kills it, and a test that takes seconds
to build its input and kills few mutants is paid by every mutant the tests
after it would have killed.  The tests whose cost is the input's, a DBC with
one list past a size bound or text at the cap through the kernel, carry
``COSTLY_TAG`` and are the last the binary lists.  Before a leg's runner
starts, the lane lists the binary's tests and refuses one that lists a tagged
test ahead of an untagged one, or no tagged test at all, since a tag dropped
from every test would otherwise pass in silence.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, NamedTuple, NewType, TypedDict, cast

from tools._common import run_capture

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from collections.abc import Sequence
    from pathlib import Path

    from tools.mutation_cpp import SweepEnvironment

# A test case's name, and one of its tags, as Catch2 lists them.
CaseName = NewType("CaseName", str)
CatchTag = NewType("CatchTag", str)

# The tag on a test the binary runs after every untagged one; ``[costly]`` in
# the source, where Catch2 lists it bare.
COSTLY_TAG = CatchTag("costly")

# What the binary prints under ``--list-tests`` with the JSON reporter.
Listing = NewType("Listing", str)


class ListedCase(TypedDict):
    """One test as the JSON listing spells it."""

    name: CaseName
    tags: list[CatchTag]


class Listings(TypedDict):
    """The listing's one section the lane reads."""

    tests: list[ListedCase]


class ListingDocument(TypedDict):
    """The JSON reporter's document, at the key the listing is under."""

    listings: Listings


class ListedTest(NamedTuple):
    """One test in the order the binary runs it: its name and its tags."""

    name: CaseName
    tags: tuple[CatchTag, ...]

    @property
    def costly(self) -> bool:
        """Whether the test carries the tag the tail is held to."""
        return COSTLY_TAG in self.tags


def listed_tests(listing: Listing) -> list[ListedTest] | Prose:
    """Read the tests a listing names, in order, or say why the text is no listing."""
    try:
        document = cast("ListingDocument", json.loads(listing))
        cases = document["listings"]["tests"]
    except json.JSONDecodeError, KeyError, TypeError:
        return Prose("order: the test binary printed no listing of its tests")
    if not cases:
        return Prose("order: the test binary's listing names no test")
    return [ListedTest(case["name"], tuple(case["tags"])) for case in cases]


def misplaced_costly_tests(tests: Sequence[ListedTest]) -> Prose | None:
    """Say which untagged test runs after a tagged one, or that no test is tagged, or None.

    Every tagged test must follow every untagged one, so the first untagged
    test after the first tagged one is the one named.
    """
    first_costly = next((index for index, test in enumerate(tests) if test.costly), None)
    if first_costly is None:
        return Prose(f"order: no test carries [{COSTLY_TAG}], so none runs last")
    late = [test.name for test in tests[first_costly:] if not test.costly]
    if not late:
        return None
    first = tests[first_costly].name
    said = f"order: {len(late)} test(s) without [{COSTLY_TAG}] run after {first!r},"
    return Prose(f"{said} the first with it: {late[0]!r}")


def order_refusal(binary: Path, *, cwd: Path, environment: SweepEnvironment) -> Prose | None:
    """List the binary's tests as the lane runs them and hold the tail to the rule.

    Run in the leg's own directory and environment, as the runner is, so the
    binary lists what the runner runs.
    """
    listed = run_capture(
        [str(binary), "--list-tests", "--order", "decl", "--reporter", "json"],
        cwd=cwd,
        env=environment.variables(),
    )
    tests = listed_tests(Listing(listed.stdout))
    if not isinstance(tests, list):
        return tests
    return misplaced_costly_tests(tests)
