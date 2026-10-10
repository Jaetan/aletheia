# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the ``fuzz_targets`` arm of the documentation gate.

Each test plants a tree holding the Go standard, the binding's
fuzz targets, a workflow and a tool, then plants one defect the arm must name:
targets the standard names and the binding lacks, targets the binding defines
and the standard does not name, a tracked workflow or tool that starts a fuzz
run, even one that is not UTF-8, and the vacuous shapes where the standard names
no target, the target file defines none, or either file is not tracked. The clean
tree and a fuzz command in a file that is no workflow or tool yield no finding.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _planted_tree import run_planted

from tools._common import RelPath
from tools.docs_arms.fuzz_targets import findings

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

DOC = RelPath("AGENTS/go.md")
TARGETS = RelPath("go/aletheia/fuzz_test.go")
WORKFLOW = RelPath(".github/workflows/go.yml")
TOOL = RelPath("tools/run_go.py")

# The standard names its targets; its fenced command is not a scheduled run.
STANDARD = Prose(
    """# Go

Fuzz targets: `FuzzParseResponse` and `FuzzMarshalCommand`.
Fuzzing is a command someone types:

```bash
go test -fuzz=Fuzz -fuzztime=60s ./aletheia/
```
"""
)
# The same standard naming four more targets, out of name order, that the binding does not define.
STANDARD_NAMING_GHOSTS = Prose(
    """# Go

Fuzz targets: `FuzzParseResponse`, `FuzzMarshalCommand`, `FuzzDelta`, `FuzzAlpha`,
`FuzzCharlie` and `FuzzBravo`.
Fuzzing is a command someone types:

```bash
go test -fuzz=Fuzz -fuzztime=60s ./aletheia/
```
"""
)
# The binding's own usage comment carries the command too, and is not a scheduled run.
GO_SOURCE = Prose(
    """package aletheia

import "testing"

// go test -fuzz=FuzzParseResponse -fuzztime=60s ./aletheia/
func FuzzParseResponse(f *testing.F) {}

func FuzzMarshalCommand(f *testing.F) {}
"""
)
WORKFLOW_TEXT = Prose(
    "name: go\non: push\njobs:\n  test:\n    steps:\n      - run: go test ./...\n"
)
TOOL_TEXT = Prose('"""Runs the Go suite."""\n\nCOMMAND = ["go", "test", "./..."]\n')
# Four target names out of name order, and the order the arm reports them in.
EXTRA_TARGETS = ("FuzzDelta", "FuzzAlpha", "FuzzCharlie", "FuzzBravo")
EXTRA_TARGETS_IN_NAME_ORDER = ("FuzzAlpha", "FuzzBravo", "FuzzCharlie", "FuzzDelta")


def _write(repo: Path, rel: RelPath, text: Prose) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    _ = path.write_text(text, encoding="utf-8")


def _repo(tmp_path: Path) -> Path:
    """Return a planted tree whose standard and binding agree and nothing fuzzes."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _write(repo, DOC, STANDARD)
    _write(repo, TARGETS, GO_SOURCE)
    _write(repo, WORKFLOW, WORKFLOW_TEXT)
    _write(repo, TOOL, TOOL_TEXT)
    return repo


def _run(repo: Path) -> list[Prose]:
    return run_planted(findings, repo)


def _schedule_finding(rel: RelPath) -> Prose:
    return Prose(f"{rel}: invokes a fuzz run, while {DOC} says fuzzing is a command one types")


def test_clean_tree_has_no_finding(tmp_path: Path) -> None:
    """The standard names the binding's targets, both ways, and nothing fuzzes on a schedule."""
    assert _run(_repo(tmp_path)) == list[Prose]()


def test_targets_named_but_not_defined(tmp_path: Path) -> None:
    """Targets the binding lacks are findings on the standard naming them, in name order."""
    repo = _repo(tmp_path)
    _write(repo, DOC, STANDARD_NAMING_GHOSTS)
    assert _run(repo) == [
        Prose(f"{DOC}: names fuzz target `{name}`, which {TARGETS} does not define")
        for name in EXTRA_TARGETS_IN_NAME_ORDER
    ]


def test_targets_defined_but_not_named(tmp_path: Path) -> None:
    """Targets the standard omits are findings on the binding defining them, in name order."""
    repo = _repo(tmp_path)
    extra = "".join(f"\nfunc {name}(f *testing.F) {{}}\n" for name in EXTRA_TARGETS)
    _write(repo, TARGETS, Prose(GO_SOURCE + extra))
    assert _run(repo) == [
        Prose(f"{TARGETS}: defines fuzz target `{name}`, which {DOC} does not name")
        for name in EXTRA_TARGETS_IN_NAME_ORDER
    ]


def test_workflow_that_fuzzes_on_a_schedule(tmp_path: Path) -> None:
    """A tracked workflow invoking a fuzz run contradicts the standard and is named."""
    repo = _repo(tmp_path)
    _write(repo, WORKFLOW, Prose(WORKFLOW_TEXT + "      - run: go test -fuzz=Fuzz -fuzztime=60s\n"))
    assert _run(repo) == [_schedule_finding(WORKFLOW)]


def test_tool_that_fuzzes(tmp_path: Path) -> None:
    """A tracked tool passing a fuzz duration contradicts the standard and is named."""
    repo = _repo(tmp_path)
    _write(repo, TOOL, Prose(TOOL_TEXT + 'FUZZ = ["go", "test", "-fuzztime=1h"]\n'))
    assert _run(repo) == [_schedule_finding(TOOL)]


def test_tool_that_is_not_utf8_is_still_scanned(tmp_path: Path) -> None:
    """A tool holding a byte that is not UTF-8 is read all the same, and its fuzz run is named."""
    repo = _repo(tmp_path)
    _ = (repo / TOOL).write_bytes(
        bytes(TOOL_TEXT, "utf-8") + b'# \xff\nFUZZ = ["go", "test", "-fuzztime=1h"]\n'
    )
    assert _run(repo) == [_schedule_finding(TOOL)]


def test_fuzz_command_in_a_github_file_that_is_no_workflow(tmp_path: Path) -> None:
    """A file under .github that is not a workflow is not read, so its fuzz command is no run."""
    repo = _repo(tmp_path)
    _write(
        repo,
        RelPath(".github/PULL_REQUEST_TEMPLATE.md"),
        Prose("- [ ] I ran `go test -fuzz=FuzzParseResponse -fuzztime=60s ./aletheia/`\n"),
    )
    assert _run(repo) == list[Prose]()


@pytest.mark.parametrize(
    ("rel", "text"),
    [
        (
            WORKFLOW,
            Prose(WORKFLOW_TEXT + "      - run: go test -fuzz FuzzA -run '^$' ./aletheia/\n"),
        ),
        (TOOL, Prose(TOOL_TEXT + 'FUZZ = ["go", "test", "-fuzz", "FuzzA"]\n')),
    ],
)
def test_target_selected_as_the_next_argument(tmp_path: Path, rel: RelPath, text: Prose) -> None:
    """The target flag followed by its value as the next argument starts a fuzz run too."""
    repo = _repo(tmp_path)
    _write(repo, rel, text)
    assert _run(repo) == [_schedule_finding(rel)]


@pytest.mark.parametrize(
    "line",
    [
        Prose('CHECKS = ["check-fuzz-targets"]'),
        Prose('ARGS = ["-fuzz_cache"]'),
        Prose('ARGS = ["-fuzz2"]'),
        Prose('ARGS = ["-fuzzer"]'),
        Prose('ARGS = ["-fuzzX"]'),
        Prose('ARGS = ["-FUZZ"]'),
        Prose("# run the fuzz harness by hand"),
    ],
)
def test_a_word_containing_the_flag_spelling_is_not_a_fuzz_run(tmp_path: Path, line: Prose) -> None:
    """The flag run into a longer word, or the bare word without its dash, is no fuzz flag."""
    repo = _repo(tmp_path)
    _write(repo, TOOL, Prose(f"{TOOL_TEXT}{line}\n"))
    assert _run(repo) == list[Prose]()


def test_a_commented_out_target_is_not_defined(tmp_path: Path) -> None:
    """A target the binding comments out is not one it defines, so the standard need not name it."""
    repo = _repo(tmp_path)
    _write(repo, TARGETS, Prose(GO_SOURCE + "\n// func FuzzOld(f *testing.F) {}\n"))
    assert _run(repo) == list[Prose]()


def test_fuzz_command_in_prose_elsewhere_is_not_a_schedule(tmp_path: Path) -> None:
    """The fuzz command the standard and the binding's own comment show is not a scheduled run."""
    repo = _repo(tmp_path)
    _write(
        repo,
        RelPath("docs/FUZZING.md"),
        Prose("Run `go test -fuzz=FuzzParseResponse -fuzztime=60s`.\n"),
    )
    assert _run(repo) == list[Prose]()


def test_standard_naming_no_target_is_a_finding(tmp_path: Path) -> None:
    """A standard with no backticked target name is a scan that matched nothing, not a pass."""
    repo = _repo(tmp_path)
    _write(repo, DOC, Prose("# Go\n\nFuzzing is a command someone types.\n"))
    assert _run(repo) == [
        Prose(f"{DOC}: names no backticked Fuzz target, so nothing was compared"),
        Prose(f"{TARGETS}: defines fuzz target `FuzzMarshalCommand`, which {DOC} does not name"),
        Prose(f"{TARGETS}: defines fuzz target `FuzzParseResponse`, which {DOC} does not name"),
    ]


def test_target_file_defining_no_target_is_a_finding(tmp_path: Path) -> None:
    """A target file that defines no target is a scan that matched nothing, named against it."""
    repo = _repo(tmp_path)
    _write(repo, TARGETS, Prose('package aletheia\n\nimport "testing"\n'))
    assert _run(repo) == [
        Prose(f"{TARGETS}: defines no Fuzz target, so nothing was compared"),
        Prose(f"{DOC}: names fuzz target `FuzzMarshalCommand`, which {TARGETS} does not define"),
        Prose(f"{DOC}: names fuzz target `FuzzParseResponse`, which {TARGETS} does not define"),
    ]


def test_missing_target_file_is_a_finding(tmp_path: Path) -> None:
    """A tree that does not track the fuzz target file leaves the claim unchecked: it is named."""
    repo = _repo(tmp_path)
    (repo / TARGETS).unlink()
    assert _run(repo) == [
        Prose(f"{TARGETS}: not tracked, so the targets {DOC} names are unchecked")
    ]


def test_missing_standard_is_a_finding(tmp_path: Path) -> None:
    """A tree that does not track the Go standard leaves its fuzz targets unchecked: it is named."""
    repo = _repo(tmp_path)
    (repo / DOC).unlink()
    assert _run(repo) == [Prose(f"{DOC}: not tracked, so its fuzz targets are unchecked")]


def test_target_selected_with_an_equals_sign(tmp_path: Path) -> None:
    """The target flag joined to its value by an equals sign starts a fuzz run."""
    repo = _repo(tmp_path)
    _write(repo, TOOL, Prose(TOOL_TEXT + 'FUZZ = ["go", "test", "-fuzz=FuzzA", "./aletheia/"]\n'))
    assert _run(repo) == [_schedule_finding(TOOL)]


@pytest.mark.parametrize(
    ("rel", "expected"),
    [
        pytest.param(
            DOC,
            [
                Prose(f"{DOC}: could not be read, so what it says is unchecked"),
                Prose(f"{DOC}: could not be read, so its fuzz targets are unchecked"),
            ],
            id="standard",
        ),
        pytest.param(
            TARGETS,
            [Prose(f"{TARGETS}: could not be read, so the targets {DOC} names are unchecked")],
            id="targets",
        ),
        pytest.param(
            WORKFLOW,
            [
                Prose(
                    f"{WORKFLOW}: could not be read, so whether it invokes a fuzz run is unchecked"
                )
            ],
            id="workflow",
        ),
        pytest.param(
            TOOL,
            [Prose(f"{TOOL}: could not be read, so whether it invokes a fuzz run is unchecked")],
            id="tool",
        ),
    ],
)
def test_a_tracked_file_the_work_tree_lacks_is_a_finding(
    tmp_path: Path, rel: RelPath, expected: list[Prose]
) -> None:
    """Each file the arm reads, tracked and gone from the work tree, is named as unread."""
    repo = _repo(tmp_path)
    (repo / rel).unlink()
    assert run_planted(findings, repo, absent={rel}) == expected


def test_an_unread_scheduling_file_leaves_the_others_scanned(tmp_path: Path) -> None:
    """A workflow the work tree lacks is named, and the tool after it is still read."""
    repo = _repo(tmp_path)
    (repo / WORKFLOW).unlink()
    _write(repo, TOOL, Prose(TOOL_TEXT + 'FUZZ = ["go", "test", "-fuzztime=1h"]\n'))
    assert run_planted(findings, repo, absent={WORKFLOW}) == [
        Prose(f"{WORKFLOW}: could not be read, so whether it invokes a fuzz run is unchecked"),
        _schedule_finding(TOOL),
    ]
