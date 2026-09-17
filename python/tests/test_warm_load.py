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
from typing import TYPE_CHECKING

import pytest

from tools._warm import read_load

if TYPE_CHECKING:
    from collections.abc import Iterator


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
