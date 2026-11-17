# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The check runner refuses a result lacking a field the kernel writes on it.

The kernel writes ``timestamp`` and ``reason`` on every fails result and
``reason`` on every unresolved one; the runner reads them as given and raises
:class:`aletheia.ProtocolError` naming a missing one rather than putting a
value of its own in its place.  The client the runner is handed answers the
log's one frame and the stream end with a plain dict, so no kernel runs.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal

import pytest
from _stream_helpers import run_checks_over_one_frame

from aletheia import ProtocolError
from aletheia.checks import signal

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.checks_runner import CheckRunResult
    from aletheia.types import (
        CompleteResponse,
        PropertyResultEntry,
    )

# Building the one check renders its threshold through the kernel renderer,
# which needs a live GHC runtime.
pytestmark = pytest.mark.usefixtures("rts_up")

_HOLDS: PropertyResultEntry = {"type": "property", "status": "holds", "property_index": 0}
_COMPLETE: CompleteResponse = {"status": "complete", "results": [], "warnings": []}


def _run(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    frame: PropertyResultEntry,
    complete: CompleteResponse,
) -> CheckRunResult:
    """Run one check over a one-frame log, the frame answered *frame* and the end *complete*."""
    checks = [signal("Speed").never_exceeds(220)]
    return run_checks_over_one_frame(tmp_path, monkeypatch, checks, frame, complete)


def test_a_fails_entry_without_its_reason_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A frame's fails entry lacking ``reason`` raises ProtocolError naming the field."""
    entry: PropertyResultEntry = {
        "type": "property",
        "status": "fails",
        "property_index": 0,
        "timestamp": 0,
    }
    with pytest.raises(ProtocolError) as excinfo:
        _ = _run(tmp_path, monkeypatch, entry, _COMPLETE)
    assert str(excinfo.value) == "reply results/reason: expected string, got nothing"


def test_a_fails_entry_without_its_timestamp_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A frame's fails entry lacking ``timestamp`` raises ProtocolError naming the field."""
    entry: PropertyResultEntry = {
        "type": "property",
        "status": "fails",
        "property_index": 0,
        "reason": "kernel reason",
    }
    with pytest.raises(ProtocolError) as excinfo:
        _ = _run(tmp_path, monkeypatch, entry, _COMPLETE)
    assert str(excinfo.value) == "reply results/timestamp: expected number, got nothing"


@pytest.mark.parametrize("status", ["fails", "unresolved"])
def test_an_end_of_stream_result_without_its_reason_is_refused(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, status: Literal["fails", "unresolved"]
) -> None:
    """An end-of-stream *status* result lacking ``reason`` raises ProtocolError naming the field."""
    result: PropertyResultEntry = {
        "type": "property",
        "status": status,
        "property_index": 0,
        "timestamp": 0,
    }
    complete: CompleteResponse = {"status": "complete", "results": [result], "warnings": []}
    with pytest.raises(ProtocolError) as excinfo:
        _ = _run(tmp_path, monkeypatch, _HOLDS, complete)
    assert str(excinfo.value) == "reply results/reason: expected string, got nothing"
