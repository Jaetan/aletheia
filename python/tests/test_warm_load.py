# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The warm Cmd_load reader: a silent agda is reported with how long it was silent.

``read_load`` is pure over a line source, so the two terminals it distinguishes
are driven here with synthetic lines: the success terminal, and the silence
that stands for a wedged process or a module checking past the budget.
"""

from __future__ import annotations

import json
import queue
from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, NewType, Self

import pytest

from tools import _warm
from tools._warm import LoadResult, describe_exit, read_load, run_warm_gate

from aletheia.common_types import ExitStatus, Prose

if TYPE_CHECKING:
    from collections.abc import Generator, Iterator
    from types import TracebackType


def _lines(*payloads: dict[str, object]) -> Iterator[str]:
    return (json.dumps(p) for p in payloads)


def test_success_terminal_sets_ok() -> None:
    """Status{checked:true} followed by InteractionPoints is a checked module."""
    source = _lines({"kind": "Status", "status": {"checked": True}}, {"kind": "InteractionPoints"})
    state = read_load(lambda: next(source))
    assert state.ok
    assert state.error == ""


def test_silence_names_the_budget() -> None:
    """A read that times out yields ok False and an error naming the seconds waited."""

    def silent() -> str | None:
        raise queue.Empty

    state = read_load(silent, silence_s=1800.0)
    assert not state.ok
    assert "no output for 1800s" in state.error


def test_eof_mid_load_raises() -> None:
    """A process that exits before its terminal is an error, not a quiet failure."""
    with pytest.raises(RuntimeError, match="exited unexpectedly"):
        _ = read_load(lambda: None)


def test_eof_mid_load_says_how_agda_ended() -> None:
    """The error carries what the process left: a heap cap reached reads as one."""
    ended = describe_exit(ExitStatus(251), _HEAP_EXHAUSTED)
    expected = r"exited unexpectedly: exit status 251; .*Heap exhausted"
    with pytest.raises(RuntimeError, match=expected):
        _ = read_load(lambda: None, exit_reason=lambda: ended)


# What agda's runtime writes when its heap cap is reached, as it wrote it under the warm cap.
_HEAP_EXHAUSTED = Prose(
    "agda: Heap exhausted;\n"
    + "agda: Current maximum heap size is 8589934592 bytes (8192 MB).\n"
    + "agda: Use `+RTS -M<size>' to increase it.\n"
)


def test_describe_exit_names_the_status_and_the_last_error_lines() -> None:
    """The status leads, then the error output's last non-blank lines in order."""
    assert describe_exit(ExitStatus(251), _HEAP_EXHAUSTED) == (
        "exit status 251; its error output ends: agda: Heap exhausted; | "
        + "agda: Current maximum heap size is 8589934592 bytes (8192 MB). | "
        + "agda: Use `+RTS -M<size>' to increase it."
    )


def test_describe_exit_keeps_the_last_five_lines() -> None:
    """A long error output is cut to its end, where agda states why it stopped."""
    output = Prose("\n".join(f"line {n}" for n in range(1, 9)) + "\n\n")
    assert describe_exit(ExitStatus(1), output) == (
        "exit status 1; its error output ends: line 4 | line 5 | line 6 | line 7 | line 8"
    )


def test_describe_exit_without_error_output_names_the_status_alone() -> None:
    """A process that wrote nothing is reported by its status, and one not yet ended says so."""
    assert describe_exit(ExitStatus(9), Prose("  \n")) == "exit status 9"
    assert describe_exit(None, Prose("")) == "still running"


# A file the warm process is asked to load, by its absolute path.
LoadedPath = NewType("LoadedPath", str)


@dataclass
class _Warm:
    """A warm process stood in: it records each file it is asked to load."""

    loaded: list[LoadedPath] = field(default_factory=list[LoadedPath])

    def __call__(self) -> Self:
        """Stand for ``WarmAgda()``: the process the gate opens."""
        return self

    def __enter__(self) -> Self:
        """Open nothing."""
        return self

    def __exit__(
        self,
        _kind: type[BaseException] | None,
        _error: BaseException | None,
        _trace: TracebackType | None,
    ) -> None:
        """Close nothing."""

    def load(self, abspath: LoadedPath) -> LoadResult:
        """Record the file and answer that it checked."""
        self.loaded.append(abspath)
        return LoadResult(tokens=[], ok=True, error="", warnings=[])


@contextmanager
def _unlocked(*, wait: bool) -> Generator[None]:
    """Stand for the agda-tree lock, taking nothing."""
    del wait
    yield


def test_each_file_the_warm_gate_loads_is_reported(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """The gate reports on stderr before the first load and as each scoped file is loaded."""
    warm = _Warm()
    monkeypatch.setattr(_warm, "WarmAgda", warm)
    monkeypatch.setattr(_warm, "agda_tree_lock", _unlocked)
    assert run_warm_gate(["A.agda", "B.agda"], lambda _agda, _files: 0, wait_lock=False) == 0
    assert [path.rsplit("/", 1)[-1] for path in warm.loaded] == ["A.agda", "B.agda"]
    assert capsys.readouterr().err == (
        "progress: 0/2 files loaded\nprogress: 1/2 files loaded\nprogress: 2/2 files loaded\n"
    )
