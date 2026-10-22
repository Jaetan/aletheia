# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The command line prints WARNING-level events to stderr for its run, and nothing below.

The Go and C++ command lines attach the same logger; the three are held alike,
one test per command line, because no shared subcommand can raise a warning
from a fixture (an unknown CAN id is refused before the kernel is reached).
"""

from __future__ import annotations

import logging
from typing import TYPE_CHECKING

import pytest

from aletheia.cli import main, warning_handler
from aletheia.client._log import LogEvent, log_event
from aletheia.common_types import ExitStatus

if TYPE_CHECKING:
    import argparse
    from collections.abc import Iterator

    from aletheia.common_types import Prose


@pytest.fixture(name="aletheia_logger")
def aletheia_logger_at_debug() -> Iterator[logging.Logger]:
    """Give the package logger letting every level through, so the handler's own level is tested."""
    logger = logging.getLogger("aletheia")
    level = logger.level
    logger.setLevel(logging.DEBUG)
    yield logger
    logger.setLevel(level)


def test_the_warning_handler_writes_warnings_alone(
    aletheia_logger: logging.Logger, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A WARNING record reaches stderr as its message; an INFO record does not."""
    handler = warning_handler()
    aletheia_logger.addHandler(handler)
    try:
        log_event(aletheia_logger, logging.INFO, LogEvent.DBC_PARSED, messages=1)
        log_event(aletheia_logger, logging.WARNING, LogEvent.CACHE_FULL, size=256)
        log_event(
            aletheia_logger,
            logging.WARNING,
            LogEvent.EXTRACTION_PARSE_FAILED,
            canId=256,
            error="bad frame",
        )
    finally:
        aletheia_logger.removeHandler(handler)
    assert (
        capsys.readouterr().err
        == "cache.full size=256\nextraction.parse_failed canId=256 error=bad frame\n"
    )


def test_the_warning_handler_writes_a_boolean_as_true_or_false(
    aletheia_logger: logging.Logger, capsys: pytest.CaptureFixture[Prose]
) -> None:
    """A boolean field reads as the Go and C++ command lines write it.

    No WARNING event carries a boolean, so a DEBUG event's fields stand in.
    """
    handler = warning_handler()
    aletheia_logger.addHandler(handler)
    try:
        for can_id, extended in ((256, False), (0x1FFFFFFF, True)):
            log_event(
                aletheia_logger,
                logging.WARNING,
                LogEvent.FRAME_PROCESSED,
                canId=can_id,
                extended=extended,
            )
    finally:
        aletheia_logger.removeHandler(handler)
    assert capsys.readouterr().err == (
        "frame.processed canId=256 extended=false\n"
        + "frame.processed canId=536870911 extended=true\n"
    )


def test_main_attaches_the_handler_for_the_run_and_takes_it_off(
    aletheia_logger: logging.Logger,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[Prose],
) -> None:
    """A warning logged while a subcommand runs reaches stderr; the handler leaves with the run."""

    def warns(_args: argparse.Namespace) -> ExitStatus:
        log_event(aletheia_logger, logging.WARNING, LogEvent.CACHE_FULL, size=256)
        return ExitStatus(0)

    monkeypatch.setattr("aletheia.cli._COMMANDS", {"validate": warns})
    before = list(aletheia_logger.handlers)
    assert main(["validate", "--dbc", "unread.dbc"]) == 0
    assert capsys.readouterr().err == "cache.full size=256\n"
    assert aletheia_logger.handlers == before
