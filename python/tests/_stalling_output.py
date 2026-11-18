# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""A watched command's output read for real, on a clock a test moves: a stall without a wait.

:func:`stall_after_first_output` makes ``tools._watchdog.watched_output`` answer
the first wait with the command's own output, so its first report is read, and
every later wait by moving the test's clock past it, so the command's deadline
passes at once and nothing waits on a time.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from tools import _watchdog
from tools._watchdog import Output, Seconds

if TYPE_CHECKING:
    import pytest

    from tools._common import Descriptor


def stall_after_first_output(monkeypatch: pytest.MonkeyPatch) -> None:
    """Make every watched command stall once its first output is read, for the rest of the test."""
    clock = [Seconds(0.0)]
    really = _watchdog.watched_output

    def scripted(out: Descriptor) -> Output:
        real, waits = really(out), [0]

        def readable_within(wait: Seconds | None) -> bool:
            waits[0] += 1
            if waits[0] == 1 or wait is None:
                return real.readable_within(None)
            clock[0] = Seconds(clock[0] + wait)
            return False

        return Output(real.read, readable_within, lambda: clock[0])

    monkeypatch.setattr(_watchdog, "watched_output", scripted)
