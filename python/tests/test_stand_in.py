# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Tests for the held build in ``tests/_stand_in.py``.

The helper waits on a FIFO for the build to say it started, and no clock
bounds that wait, so what is held here is that a driver which never gets as
far as its build ends the wait with a failure rather than leaving the suite
blocked: under mutmut's copied tree, for one, the driver cannot import the
gates it runs.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from _stand_in import ScriptSource, driving_a_held_build

if TYPE_CHECKING:
    from pathlib import Path


@pytest.mark.process(
    "the wait ends at the end of file a driver's exit leaves on the FIFO, which only a"
    + " driver process that exits shows"
)
@pytest.mark.parametrize(
    "source", [ScriptSource("raise SystemExit(3)"), ScriptSource("this is not Python")]
)
def test_a_driver_that_ends_before_its_build_fails_the_wait(
    tmp_path: Path, source: ScriptSource
) -> None:
    """A driver that exits before starting any build, or before running a line, fails the wait.

    A source that does not compile ends the driver before any line of it runs.
    """
    with (
        pytest.raises(AssertionError, match="the driver ended before the build it runs started"),
        driving_a_held_build(tmp_path, source),
    ):
        pass
