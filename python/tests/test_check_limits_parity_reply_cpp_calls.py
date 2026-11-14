# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate counts a C++ call comparing a word as the Go and Rust readers do.

A reader file comparing a text by a call outside the dispatches is named at
the call's name: ``starts_with``, ``ends_with``, a ``compare`` member, and a
std::string's or a std::string_view's ``find`` or ``contains``, unless every
argument it is given is a string literal holding no word.  A Json's
``contains`` or ``find`` looks a key up, and ``find_first_of`` and its
siblings take a set of characters, so neither compares a word.  An equality
called by its name, ``std::operator==``, is read as one written infix: named
at its operator outside the dispatches, an arm inside one.  Inside a dispatch
every search is counted, one given a literal of no word too.  The cases share
one parse.
"""

from __future__ import annotations

import pytest
from _cpp_reply_gate import (
    Plant,
    after_signal_name,
    gate_report,
    named_at,
    planted_line,
    unparsed,
    unplaced,
)

from tools._reply_places import CppText, ReplyPlace
from tools._reply_places_cpp import CPP_PARSE_DBC

from aletheia.common_types import Prose

_IN_DBC = "cpp/src/json_parse_dbc.cpp:"
_OUTSIDE = "compares a word outside the dispatches CPP_REPLY_TEXT names"

# The conditions read_signal is planted with on its name, each on a line of its
# own: those the gate counts, then those it passes over.
_COUNTED = tuple(
    map(
        CppText,
        (
            'name.find("holds") != std::string::npos',
            'name.contains("holds")',
            'std::string_view{name}.find("holds") != std::string_view::npos',
            'std::string_view{name}.contains("holds")',
            'name.find("-", 1) != std::string::npos',
            "name.ends_with(name)",
            'std::operator==(std::string_view{name}, "holds")',
            'std::operator!=(std::optional<std::string>{name}, "holds")',
        ),
    )
)
_PASSED = tuple(
    map(
        CppText,
        (
            'name.starts_with("-")',
            'name.ends_with("a-b")',
            'name.compare("-") == 0',
            'name.find("-") != std::string::npos',
            'name.contains("-")',
            'j.contains("holds")',
            'j.find("holds") != j.end()',
            'name.find_first_of("ab") != std::string::npos',
            'name.find_last_of("ab") != std::string::npos',
            'name.find_first_not_of("ab") != std::string::npos',
            'name.find_last_not_of("ab") != std::string::npos',
        ),
    )
)

# The conditions in read_signal; an equality read_attr_type calls by its name;
# a search read_comment_target gives a literal of no word.
_CALLS = (
    after_signal_name(
        CppText("".join(f"    if ({call}) {{}}\n" for call in (*_COUNTED, *_PASSED)))
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "int")\n        return DbcAttrTypeInt'),
        CppText('if (std::operator==(kind, "int"))\n        return DbcAttrTypeInt'),
    ),
    Plant(
        CPP_PARSE_DBC,
        CppText('if (kind == "network")\n        return DbcCommentTargetNetwork{};'),
        CppText(
            'if (std::string{"-"}.starts_with("-")) {}\n'
            + '    if (kind == "network")\n        return DbcCommentTargetNetwork{};'
        ),
    ),
)


def _named_on(found: list[Prose], call: CppText) -> list[Prose]:
    """Return what the gate names, at no place, on the line testing ``call``."""
    line = planted_line(_CALLS, CPP_PARSE_DBC, CppText(f"if ({call}) {{}}"))
    return [each for each in unplaced(found) if each.startswith(f"{_IN_DBC}{line}:")]


@pytest.mark.parametrize("call", [pytest.param(call, id=call) for call in _COUNTED])
def test_a_call_comparing_a_word_outside_the_dispatches_is_named_at_its_line(
    monkeypatch: pytest.MonkeyPatch, call: CppText
) -> None:
    """A search of a text given what may hold a word, or an equality called by name, is named."""
    found = gate_report(monkeypatch, _CALLS)
    assert unparsed(found) == []
    line = planted_line(_CALLS, CPP_PARSE_DBC, CppText(f"if ({call}) {{}}"))
    written = f"if ({call}) {{}}"
    assert _named_on(found, call) == [Prose(f"{_IN_DBC}{line}: {written!r} {_OUTSIDE}")]


@pytest.mark.parametrize("call", [pytest.param(call, id=call) for call in _PASSED])
def test_a_call_comparing_no_word_is_not_named(
    monkeypatch: pytest.MonkeyPatch, call: CppText
) -> None:
    """A search given literals of no word, a Json's key lookup or a character set compares none."""
    found = gate_report(monkeypatch, _CALLS)
    assert unparsed(found) == []
    assert _named_on(found, call) == []


def test_an_equality_called_by_its_name_is_an_arm_of_the_dispatch_it_stands_in(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """``std::operator==(kind, "int")`` gives read_attr_type its arm, as ``kind == "int"`` does."""
    found = gate_report(monkeypatch, _CALLS)
    assert unparsed(found) == []
    assert named_at(found, ReplyPlace("dbc/attributes/attrType/kind")) == []


def test_a_dispatch_counts_a_search_given_a_literal_of_no_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A search in a dispatch compares a text other than its word, whatever its literal holds."""
    found = gate_report(monkeypatch, _CALLS)
    assert unparsed(found) == []
    assert named_at(found, ReplyPlace("dbc/comments/target/kind")) == [
        Prose(
            f"{_IN_DBC}read_comment_target: "
            + "compares a word other than the one at 'kind' with == to a literal"
        )
    ]
