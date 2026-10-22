# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Every checks file shipped or shown with a DBC runs against that DBC to a verdict.

The documents show each shipped checks file with a DBC and a log: README, the
quickstart, the tutorial and the CLI guide run ``vehicle_checks.yaml`` against
``vehicle.dbc`` over ``drive.log``, and README's code-free line runs the
filled-in template ``demo_workbook.xlsx``, which carries its own DBC sheet,
over the same log. The quickstart and the tutorial also show a checks file in
a YAML block for the reader to run against ``vehicle.dbc``. The kernel refuses
a check naming a signal its DBC does not carry, and a run whose every check
stays unresolved also exits 0, so each run here is held to its exit status and
to exactly the checks it leaves unresolved: the checks on the messages the log
holds resolve. A checks file shipped, or a checks block a document shows,
without a pairing here fails the completeness case, which names those shown
with no DBC.
"""

from __future__ import annotations

import json
import re
from typing import TYPE_CHECKING, NamedTuple, NewType

import pytest
from _cli_check_helpers import REPO_ROOT, CheckInputs, report, run_check, skip_without_ffi

from tools._common import RelPath, git_ls_files
from tools._markdown import fences, headings

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from pathlib import Path

# A check's name, as its checks file states it and the report repeats it.
CheckLabel = NewType("CheckLabel", str)

# The file name of a checks file shipped under examples/.
ShippedFile = NewType("ShippedFile", str)

_DEMO = REPO_ROOT / "examples" / "demo"


class Pairing(NamedTuple):
    """A shipped checks file run as the documents show it, and the verdict that run ends in."""

    inputs: CheckInputs
    exit_status: ExitStatus
    unresolved: frozenset[CheckLabel]


_PAIRINGS = {
    # The matched set: drive.log speeds past the 120 kph limit.
    ShippedFile("vehicle_checks.yaml"): Pairing(
        CheckInputs(
            log=_DEMO / "drive.log",
            dbc=_DEMO / "vehicle.dbc",
            checks=_DEMO / "vehicle_checks.yaml",
            as_json=True,
        ),
        ExitStatus(1),
        frozenset(),
    ),
    # The template's DBC sheet carries drive.log's two messages and the
    # signals of its other checks, which the log never shows.
    ShippedFile("demo_workbook.xlsx"): Pairing(
        CheckInputs(log=_DEMO / "drive.log", workbook=_DEMO / "demo_workbook.xlsx", as_json=True),
        ExitStatus(0),
        frozenset(
            CheckLabel(name)
            for name in (
                "Battery voltage range",
                "Coolant settling",
                "Fault code exclusion",
                "Parking brake",
                "Battery floor",
                "Brake light",
                "Engine start",
                "Fuel warning",
            )
        ),
    ),
}

# The checks file the documents show with no DBC: demo_yaml_loader.py loads it
# and compares it with the Check API, and nothing runs it.
_SHOWN_WITHOUT_A_DBC = frozenset({ShippedFile("demo_checks.yaml")})


class ShownBlock(NamedTuple):
    """A YAML block of checks a document shows, by its document and the heading above it."""

    doc: RelPath
    heading: Prose


# The blocks a document shows as a checks file to run against vehicle.dbc.
_SHOWN_WITH_THE_DEMO_DBC = frozenset(
    {
        ShownBlock(RelPath("docs/guides/QUICKSTART.md"), Prose("1. Define Checks (YAML)")),
        ShownBlock(RelPath("docs/guides/TUTORIAL.md"), Prose("Step 1: Write a YAML Checks File")),
    }
)

# The blocks the interfaces reference shows to illustrate the schema, with no DBC.
_ILLUSTRATING_THE_SCHEMA = frozenset(
    ShownBlock(RelPath("docs/reference/INTERFACES.md"), Prose(heading))
    for heading in ("Simple Checks", "When/Then Checks", "Complete Example File", "Equivalence")
)

_CHECKS_DOCUMENT = re.compile(r"^checks:", re.MULTILINE)


def _shown_blocks(doc: RelPath) -> dict[ShownBlock, list[Prose]]:
    """Every YAML block of ``doc`` holding checks, under the heading above it, in order."""
    source = (REPO_ROOT / doc).read_text(encoding="utf-8")
    text = Prose(source)
    lines = source.splitlines()
    above = headings(text)
    shown: dict[ShownBlock, list[Prose]] = {}
    for fence in fences(text):
        if fence.info.split()[:1] != ["yaml"]:
            continue
        closing = next(n for n in range(fence.line, len(lines)) if lines[n].strip() == fence.markup)
        body = Prose("\n".join(lines[fence.line : closing]))
        if not _CHECKS_DOCUMENT.search(body):
            continue
        heading = max((h for h in above if h.line < fence.line), key=lambda h: h.line)
        shown.setdefault(ShownBlock(doc, heading.text), []).append(body)
    return shown


@pytest.mark.process(
    "git's own index decides which files are tracked, so only git lists the shipped checks"
    + " files and the documents whose checks blocks are held to a pairing"
)
def test_every_checks_file_shipped_or_shown_is_paired() -> None:
    """A checks file shipped or shown in a YAML block is run here, or is shown with no DBC."""
    tracked = git_ls_files(REPO_ROOT, "examples", "*.md")
    shipped = {
        ShippedFile(rel.rsplit("/", 1)[-1])
        for rel in tracked
        if rel.startswith("examples/") and rel.endswith((".yaml", ".xlsx"))
    }
    assert shipped == _PAIRINGS.keys() | _SHOWN_WITHOUT_A_DBC
    shown = {block for rel in tracked if rel.endswith(".md") for block in _shown_blocks(rel)}
    assert shown == _SHOWN_WITH_THE_DEMO_DBC | _ILLUSTRATING_THE_SCHEMA


@pytest.mark.parametrize("block", sorted(_SHOWN_WITH_THE_DEMO_DBC), ids=lambda block: block.doc)
def test_a_checks_file_a_document_shows_runs_to_its_verdict(
    block: ShownBlock, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The block, run as the document shows it over the demo log, resolves every check."""
    skip_without_ffi()
    (body,) = _shown_blocks(block.doc)[block]
    checks = tmp_path / "checks.yaml"
    _ = checks.write_text(body + "\n", encoding="utf-8")
    inputs = CheckInputs(
        log=_DEMO / "drive.log", dbc=_DEMO / "vehicle.dbc", checks=checks, as_json=True
    )
    result = run_check(inputs, monkeypatch)
    msg = report(result)
    # drive.log speeds past the 120 kph limit both blocks set.
    assert result.returncode == ExitStatus(1), msg
    assert json.loads(result.stdout)["unresolved"] == [], msg


@pytest.mark.parametrize("name", sorted(_PAIRINGS))
def test_a_shipped_checks_file_runs_to_its_verdict(
    name: ShippedFile, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The run ends in its verdict, with exactly the checks the log never shows unresolved."""
    skip_without_ffi()
    pairing = _PAIRINGS[name]
    result = run_check(pairing.inputs, monkeypatch)
    msg = report(result)
    assert result.returncode == pairing.exit_status, msg
    reported = json.loads(result.stdout)["unresolved"]
    assert {CheckLabel(entry["check_name"]) for entry in reported} == pairing.unresolved, msg


def test_the_readme_shows_the_excel_line_over_the_template() -> None:
    """README shows the Excel line this module runs and names the workbook as its template."""
    readme = (REPO_ROOT / "README.md").read_text(encoding="utf-8")
    assert "aletheia check --excel workbook.xlsx trace.log" in readme.splitlines()
    assert "examples/demo/demo_workbook.xlsx" in readme
