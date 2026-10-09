# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the ``fuzz_targets`` arm of the documentation gate.

Each test builds a throwaway repository holding the Go standard, the binding's
fuzz targets, a workflow and a tool, then plants one defect the arm must name:
a target the standard names and the binding lacks, a target the binding defines
and the standard does not name, a tracked workflow or tool that starts a fuzz
run, and the vacuous shapes where the standard names no target or the target
file is gone. The clean repository yields no finding.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _git_repo import commit, git

from tools._common import RelPath
from tools.check_docs import run_arm
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
# The same standard naming a third target the binding does not define.
STANDARD_NAMING_A_GHOST = Prose(
    """# Go

Fuzz targets: `FuzzParseResponse`, `FuzzMarshalCommand` and `FuzzGone`.
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


def _write(repo: Path, rel: RelPath, text: Prose) -> None:
    path = repo / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    _ = path.write_text(text, encoding="utf-8")


def _repo(tmp_path: Path) -> Path:
    """Return a committed repository whose standard and binding agree and nothing fuzzes."""
    repo = tmp_path / "repo"
    repo.mkdir()
    _ = git(repo, "init", "-q")
    _write(repo, DOC, STANDARD)
    _write(repo, TARGETS, GO_SOURCE)
    _write(repo, WORKFLOW, WORKFLOW_TEXT)
    _write(repo, TOOL, TOOL_TEXT)
    _ = commit(repo, "base")
    return repo


def _run(repo: Path) -> list[Prose]:
    return run_arm(findings, repo)


def test_clean_repository_has_no_finding(tmp_path: Path) -> None:
    """The standard names the binding's targets, both ways, and nothing fuzzes on a schedule."""
    assert _run(_repo(tmp_path)) == []


def test_target_named_but_not_defined(tmp_path: Path) -> None:
    """A target the standard names and the binding lacks is reported against the standard."""
    repo = _repo(tmp_path)
    _write(repo, DOC, STANDARD_NAMING_A_GHOST)
    _ = commit(repo, "name a target the binding lacks")
    found = _run(repo)
    assert len(found) == 1
    assert found[0].startswith(f"{DOC}: ")
    assert "FuzzGone" in found[0]
    assert "FuzzMarshalCommand" not in found[0]
    assert TARGETS in found[0]


def test_target_defined_but_not_named(tmp_path: Path) -> None:
    """A target the binding defines and the standard does not name is reported against it."""
    repo = _repo(tmp_path)
    _write(repo, TARGETS, Prose(GO_SOURCE + "\nfunc FuzzExtra(f *testing.F) {}\n"))
    _ = commit(repo, "define a target the standard does not name")
    found = _run(repo)
    assert len(found) == 1
    assert found[0].startswith(f"{TARGETS}: ")
    assert "FuzzExtra" in found[0]
    assert DOC in found[0]


def test_workflow_that_fuzzes_on_a_schedule(tmp_path: Path) -> None:
    """A tracked workflow invoking a fuzz run contradicts the standard and is named."""
    repo = _repo(tmp_path)
    _write(repo, WORKFLOW, Prose(WORKFLOW_TEXT + "      - run: go test -fuzz=Fuzz -fuzztime=60s\n"))
    _ = commit(repo, "fuzz in a workflow")
    found = _run(repo)
    assert len(found) == 1
    assert found[0].startswith(f"{WORKFLOW}: ")


def test_tool_that_fuzzes(tmp_path: Path) -> None:
    """A tracked tool passing a fuzz duration contradicts the standard and is named."""
    repo = _repo(tmp_path)
    _write(repo, TOOL, Prose(TOOL_TEXT + 'FUZZ = ["go", "test", "-fuzztime=1h"]\n'))
    _ = commit(repo, "fuzz from a tool")
    found = _run(repo)
    assert len(found) == 1
    assert found[0].startswith(f"{TOOL}: ")


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
    _ = commit(repo, "select a fuzz target with a separate argument")
    found = _run(repo)
    assert len(found) == 1
    assert found[0].startswith(f"{rel}: ")


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
    _ = commit(repo, "name a word containing the flag spelling")
    assert _run(repo) == []


def test_a_commented_out_target_is_not_defined(tmp_path: Path) -> None:
    """A target the binding comments out is not one it defines, so the standard need not name it."""
    repo = _repo(tmp_path)
    _write(repo, TARGETS, Prose(GO_SOURCE + "\n// func FuzzOld(f *testing.F) {}\n"))
    _ = commit(repo, "comment out a target")
    assert _run(repo) == []


def test_fuzz_command_in_prose_elsewhere_is_not_a_schedule(tmp_path: Path) -> None:
    """The fuzz command the standard and the binding's own comment show is not a scheduled run."""
    repo = _repo(tmp_path)
    _write(
        repo,
        RelPath("docs/FUZZING.md"),
        Prose("Run `go test -fuzz=FuzzParseResponse -fuzztime=60s`.\n"),
    )
    _ = commit(repo, "document the command")
    assert _run(repo) == []


def test_standard_naming_no_target_is_a_finding(tmp_path: Path) -> None:
    """A standard with no backticked target name is a scan that matched nothing, not a pass."""
    repo = _repo(tmp_path)
    _write(repo, DOC, Prose("# Go\n\nFuzzing is a command someone types.\n"))
    _ = commit(repo, "drop the target names")
    found = _run(repo)
    assert any(line.startswith(f"{DOC}: ") for line in found)


def test_missing_target_file_is_a_finding(tmp_path: Path) -> None:
    """A binding without the fuzz target file leaves the claim unchecked, so it is named."""
    repo = _repo(tmp_path)
    _ = git(repo, "rm", "-q", TARGETS)
    _ = commit(repo, "remove the targets")
    found = _run(repo)
    assert any(line.startswith(f"{TARGETS}: ") for line in found)


def test_missing_standard_is_a_finding(tmp_path: Path) -> None:
    """A tree without the Go standard has nothing to hold the claim against, so it is named."""
    repo = _repo(tmp_path)
    _ = git(repo, "rm", "-q", DOC)
    _ = commit(repo, "remove the standard")
    found = _run(repo)
    assert any(line.startswith(f"{DOC}: ") for line in found)


def test_target_selected_with_an_equals_sign(tmp_path: Path) -> None:
    """The target flag joined to its value by an equals sign starts a fuzz run."""
    repo = _repo(tmp_path)
    _write(repo, TOOL, Prose(TOOL_TEXT + 'FUZZ = ["go", "test", "-fuzz=FuzzA", "./aletheia/"]\n'))
    _ = commit(repo, "select a fuzz target with an equals sign")
    found = _run(repo)
    assert len(found) == 1
    assert found[0].startswith(f"{TOOL}: ")
