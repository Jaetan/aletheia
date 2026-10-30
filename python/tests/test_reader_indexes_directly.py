# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The readers index their own tables with the kernel's property index, its range unchecked.

The kernel proves every ``property_index`` it writes below the number of
properties the last accepted ``set_properties`` was handed, so the client reads
its per-property diagnostics, and the check runner its checks, at that index
directly: an index past them raises Python's own ``KeyError`` or ``IndexError``.
A check without a name is shown by its index.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, NewType

import pytest
from _stream_helpers import run_checks_over_one_frame

from aletheia import AletheiaClient, MockBackend, Signal
from aletheia.checks import signal
from aletheia.types import DLCCode

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.checks import CheckResult
    from aletheia.checks_runner import CheckRunResult
    from aletheia.types import (
        CompleteResponse,
        PropertyResultEntry,
    )

# Building a property or a check renders its threshold through the kernel
# renderer, which needs a live GHC runtime.
pytestmark = pytest.mark.usefixtures("rts_up")

# A property's position in the list ``set_properties`` was handed.
PropertyIndex = NewType("PropertyIndex", int)

_SUCCESS = json.dumps({"status": "success"}).encode("utf-8")
_COMPLETE: CompleteResponse = {"status": "complete", "results": [], "warnings": []}


def _fails(index: PropertyIndex) -> PropertyResultEntry:
    """Build a frame's fails entry for the property at *index*."""
    return {
        "type": "property",
        "status": "fails",
        "property_index": index,
        "timestamp": 0,
        "reason": "kernel reason",
    }


def _run_one_frame(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    checks: list[CheckResult],
    entry: PropertyResultEntry,
) -> CheckRunResult:
    """Run *checks* over a one-frame log, the frame answered *entry* and the end with no result."""
    return run_checks_over_one_frame(tmp_path, monkeypatch, checks, entry, _COMPLETE)


def test_a_frame_result_past_the_properties_raises_key_error() -> None:
    """A frame's fails entry indexes the diagnostics directly: one past them is ``KeyError``."""
    batch = {"type": "property_batch", "results": [_fails(PropertyIndex(1))]}
    backend = MockBackend([_SUCCESS, _SUCCESS, json.dumps(batch).encode("utf-8")])
    with AletheiaClient(backend=backend) as client:
        client.set_properties([Signal("Speed").less_than(1).always().to_dict()])
        client.start_stream()
        with pytest.raises(KeyError, match=r"^1$"):
            _ = client.send_frame(0, 0x100, DLCCode(8), bytes(8))


def test_a_check_index_past_the_checks_raises_index_error(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The check runner indexes its checks directly: one past them is ``IndexError``."""
    checks = [signal("Speed").never_exceeds(220)]
    with pytest.raises(IndexError, match=r"^list index out of range$"):
        _ = _run_one_frame(tmp_path, monkeypatch, checks, _fails(PropertyIndex(1)))


def test_a_check_without_a_name_is_shown_by_its_index(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A violation of an unnamed check carries ``Check #<index>`` and an empty severity."""
    checks = [signal("Speed").never_exceeds(220)]
    result = _run_one_frame(tmp_path, monkeypatch, checks, _fails(PropertyIndex(0)))
    assert [(v["check_name"], v["severity"]) for v in result.violations] == [("Check #0", "")]


def test_a_named_check_is_shown_by_its_name_and_severity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A violation of a named check carries the check's name and severity."""
    checks = [signal("Speed").never_exceeds(220).named("Speed limit").severity("error")]
    result = _run_one_frame(tmp_path, monkeypatch, checks, _fails(PropertyIndex(0)))
    assert [(v["check_name"], v["severity"]) for v in result.violations] == [
        ("Speed limit", "error")
    ]
