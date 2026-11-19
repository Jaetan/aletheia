# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""How a tool reports its progress to the watchdog: ``progress: <done>/<total> <what>``.

A step of the sweep reports its progress in its own output (``tools._watchdog``);
a tool of ours does it through :func:`reported`, which wraps the items its work
walks and prints a report before the first, after each item that completes
another twentieth of them, and after the last: at most 21 lines, counted by
items, never by a clock.  Each report is flushed as it is printed, so it is in
the step's file the moment it is made.  A short tool's whole work is one item:
:func:`reporting` runs it between a report as it starts and one as it ends.
:data:`REPORT` is the pattern every such step declares.
"""

from __future__ import annotations

import sys
from typing import TYPE_CHECKING, NewType

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Iterator, Sequence

    from aletheia.common_types import Prose

# The regular expression a report of :func:`reported` matches, as a step's progress declares it;
# a count of the items a tool's work walks.
ReportPattern = NewType("ReportPattern", str)
ItemCount = NewType("ItemCount", int)
REPORT = ReportPattern(r"^progress: (?P<done>\d+)/(?P<total>\d+) ")

# How many reports a walk makes between its first and its last.
_STRETCHES = 20


def report(done: ItemCount, total: ItemCount, what: Prose) -> None:
    """Print one progress report to stderr, flushed: ``done`` of ``total`` ``what``.

    Stderr, as every progress line the tools print: stdout stays the tool's
    data, read whole by whatever runs it, and the watchdog reads both.  A
    report names what it counts: the watchdog hears a line stripped, and
    :data:`REPORT` would not read one naming nothing, so ``what`` empty or
    blank is refused with :class:`ValueError`.
    """
    if not what.strip():
        message = "a progress report names what it counts"
        raise ValueError(message)
    _ = sys.stderr.write(f"progress: {done}/{total} {what}\n")
    sys.stderr.flush()


def reported[T](items: Sequence[T], what: Prose) -> Iterator[T]:
    """Yield ``items`` in order, reporting before the first, each twentieth done, and the end."""
    return counted(items, ItemCount(len(items)), what)


def counted[T](items: Iterable[T], total: ItemCount, what: Prose) -> Iterator[T]:
    """Yield ``items``, ``total`` of them, as they come, reporting as :func:`reported` does.

    For items that arrive one by one, a pool's results in order: each report is
    made as the item that completes its share arrives.
    """
    marks = {round(stretch * total / _STRETCHES) for stretch in range(1, _STRETCHES + 1)}
    report(ItemCount(0), total, what)
    for done, item in enumerate(items, 1):
        yield item
        if done in marks:
            report(ItemCount(done), total, what)


def reporting[S](main: Callable[[], S], what: Prose) -> S:
    """Run a short tool's ``main`` as one item of work: reported as it starts and as it ends."""
    report(ItemCount(0), ItemCount(1), what)
    status = main()
    report(ItemCount(1), ItemCount(1), what)
    return status
