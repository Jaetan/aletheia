# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The check runner raises a kernel refusal as the kernel's message, verbatim, with its code.

The checks, the stream start and the stream end each answer the kernel's error
envelope; the runner adds nothing before its message.  The replies are canned
through :class:`aletheia.MockBackend` on the client the runner is handed, so no
kernel runs, and the log the runner streams is empty.
"""

from __future__ import annotations

import json
from typing import TYPE_CHECKING, Literal

import pytest

from aletheia import AletheiaClient, AletheiaError, MockBackend
from aletheia._dbc_types import empty_dbc_tier2
from aletheia.checks_runner import run_checks

if TYPE_CHECKING:
    from pathlib import Path

    from aletheia.types import DBCDefinition, ErrorResponse

_REFUSAL: ErrorResponse = {"status": "error", "code": "handler_err", "message": "kernel says no"}
_SUCCESS = json.dumps({"status": "success"}).encode("utf-8")
_DBC: DBCDefinition = {"version": "", "messages": [], **empty_dbc_tier2()}

# The runner's calls on the kernel, in the order it makes them.
Step = Literal["add_checks", "start_stream", "end_stream"]
_STEPS: tuple[Step, ...] = ("add_checks", "start_stream", "end_stream")


@pytest.mark.parametrize("step", _STEPS)
def test_a_refusal_is_the_kernels_message(tmp_path: Path, step: Step) -> None:
    """A refusal of *step* raises the kernel's message verbatim with its code."""
    log = tmp_path / "frames.log"
    log.write_text("", encoding="utf-8")
    replies = [_SUCCESS] * _STEPS.index(step) + [json.dumps(_REFUSAL).encode("utf-8")]
    backend = MockBackend(replies)
    with AletheiaClient(backend=backend) as client, pytest.raises(AletheiaError) as excinfo:
        _ = run_checks(_DBC, [], str(log), client=client)
    assert str(excinfo.value) == "kernel says no", step
    assert excinfo.value.code == "handler_err", step
