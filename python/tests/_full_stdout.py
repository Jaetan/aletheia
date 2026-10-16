# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Stdout on ``/dev/full``, where every write fails for want of space, as a run sees it."""

from __future__ import annotations

import contextlib
import errno
import io
import os
import sys
from pathlib import Path
from typing import TYPE_CHECKING, Final, Literal, NamedTuple, TextIO

import pytest

if TYPE_CHECKING:
    from collections.abc import Generator

# What ``/dev/full`` answers a write, as an ``OSError`` prints it.
NO_SPACE: Final = f"[Errno {errno.ENOSPC}] {os.strerror(errno.ENOSPC)}"

# How stdout buffers what a run writes, as ``open`` takes it: by blocks, as a file
# or a pipe is, so a short report first reaches the system at the flush that ends
# the run; by lines, as a terminal is, so it reaches it at its first line; or by
# blocks shorter than the report, so the write handing the report to stdout's
# buffer reaches the system itself.
type Buffering = Literal[-1, 1, 16]
BY_BLOCKS: Final[Buffering] = -1
BY_LINES: Final[Buffering] = 1
BY_SHORT_BLOCKS: Final[Buffering] = 16
BUFFERINGS: Final[list[Buffering]] = [BY_BLOCKS, BY_LINES, BY_SHORT_BLOCKS]
BUFFERING_IDS: Final = ["by blocks", "by lines", "by short blocks"]


class Streams(NamedTuple):
    """Stdout on ``/dev/full`` and stderr kept in memory, as a run under test sees them."""

    out: TextIO
    err: io.StringIO


@contextlib.contextmanager
def full_stdout(buffering: Buffering) -> Generator[Streams]:
    """Point stdout at ``/dev/full``, buffered as ``buffering`` says, and stderr at memory.

    Entered in a test's own body, since pytest points both streams back at its
    capture as each phase of a test begins.
    """
    err = io.StringIO()
    with (
        Path("/dev/full").open("w", buffering=buffering, encoding="utf-8") as full,
        pytest.MonkeyPatch.context() as patch,
    ):
        patch.setattr(sys, "stdout", full)
        patch.setattr(sys, "stderr", err)
        yield Streams(full, err)
