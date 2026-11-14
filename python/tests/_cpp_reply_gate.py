# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate run over the C++ library with texts of its files planted.

A C++ gate test writes the library's code as its case writes it, each plant a
text standing once in a file and what it is planted as, and reads what the gate
then reports: each line the compiler refuses, each set the C++ reader cannot
read and each line comparing a word outside the dispatches, or else each
divergence from ``replyText``.  Cases planting the same texts share one parse of
each file, which the reader keeps.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, NamedTuple

from tools._reply_places import (
    AGDA_REPLY_RANGE,
    AgdaText,
    CppLine,
    CppText,
    ReplyPlace,
    check_reply_places,
    read_reply_tables,
)
from tools._reply_places_cpp import CPP_PARSE_DBC, cpp_reader

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path

    import pytest


class Plant(NamedTuple):
    """A text standing once in a file of the C++ library, and what it is planted as."""

    path: Path
    written: CppText
    planted: CppText


# How the gate ends its report of a line the compiler refuses, before the message.
UNPARSED = Prose("is not C++ libclang-23 parses")

# The line read_signal reads a signal's name at, and the line after it.
_SIGNAL_NAME = CppText('    auto name = field_string(j, path, "name");\n')
_SIGNAL_NEXT = CppText("    auto const start_bit")


def after_signal_name(lines: CppText) -> Plant:
    """Return a plant in read_signal writing LINES after the line reading the signal's name."""
    return Plant(
        CPP_PARSE_DBC,
        CppText(_SIGNAL_NAME + _SIGNAL_NEXT),
        CppText(_SIGNAL_NAME + lines + _SIGNAL_NEXT),
    )


def planted_texts(plants: tuple[Plant, ...]) -> dict[Path, CppText]:
    """Return the source of each file a plant names, every plant written into it in turn."""
    texts: dict[Path, CppText] = {}
    for plant in plants:
        if plant.path not in texts:
            texts[plant.path] = CppText(plant.path.read_text(encoding="utf-8"))
        assert texts[plant.path].count(plant.written) == 1, plant.written
        texts[plant.path] = CppText(texts[plant.path].replace(plant.written, plant.planted))
    return texts


def planted_line(plants: tuple[Plant, ...], path: Path, needle: CppText) -> CppLine:
    """Return the line ``needle`` starts on in ``path`` once ``plants`` are written."""
    source = planted_texts(plants).get(path) or CppText(path.read_text(encoding="utf-8"))
    assert source.count(needle) == 1, needle
    return CppLine(source[: source.index(needle)].count("\n") + 1)


def plant_library(monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...]) -> None:
    """Have the C++ reader read the library with ``plants`` written into it."""
    texts = planted_texts(plants)

    def source_of(path: Path) -> CppText:
        return texts[path] if path in texts else CppText(path.read_text(encoding="utf-8"))

    monkeypatch.setattr("tools._reply_places_cpp._cpp_source", source_of)


def gate_report(monkeypatch: pytest.MonkeyPatch, plants: tuple[Plant, ...]) -> list[Prose]:
    """Return what the gate reports of the C++ library with ``plants`` written into it."""
    plant_library(monkeypatch, plants)
    agda = AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8"))
    found = read_reply_tables(agda, (cpp_reader(frozenset()),))
    return found if isinstance(found, list) else check_reply_places(found, frozenset())


def unparsed(found: list[Prose]) -> list[Prose]:
    """Return each report of a line the compiler refuses."""
    return [each for each in found if UNPARSED in each]


def named_at(found: list[Prose], place: ReplyPlace) -> list[Prose]:
    """Return, sorted, what a report names at ``place``, its lead cut."""
    lead = f"reply place {place}: "
    return sorted(Prose(each.removeprefix(lead)) for each in found if each.startswith(lead))


def unplaced(found: list[Prose]) -> list[Prose]:
    """Return what a report names at no place: a line refused or read outside the readers' sets."""
    return [each for each in found if not each.startswith("reply place ")]
