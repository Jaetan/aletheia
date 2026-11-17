# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""The reply-tags gate reads a C++ word place from the table ``field_member`` reads.

``read_issue`` reads an issue's severity with ``field_member``, which refuses
every word ``severity_table`` does not name, ``read_verdict`` a result's status
from ``verdict_table``, ``read_signal`` a signal's byte order from
``byte_order_table`` and ``read_attribute`` a definition's scope from
``attr_scope_table``, so a table's words are the C++ reader's set at its places
and its last entry its last arm, which reads the words of the entries giving its
enumerator too: a word added to the table or dropped from it, a last entry other
than the row's last word or sharing its enumerator with another entry, a
reference to the table outside a ``field_member`` call, a table no such call
reads and an entry the gate cannot read are each named at the place.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

import pytest

from tools._reply_places import (
    AGDA_REPLY_RANGE,
    AgdaText,
    CppLine,
    CppText,
    ReplyPlace,
    ReplyTables,
    check_reply_places,
    read_reply_tables,
)
from tools._reply_places_cpp import CPP_PARSE, CPP_PARSE_DBC, cpp_reader

from aletheia.common_types import Prose

if TYPE_CHECKING:
    from pathlib import Path


@dataclass(frozen=True)
class _Plant:
    """A plant: ``written`` in ``path``'s source written as ``planted``."""

    path: Path
    written: CppText
    planted: CppText


_SEVERITY = (ReplyPlace("issues/severity"), ReplyPlace("warnings/severity"))
_BYTE_ORDER = (ReplyPlace("dbc/messages/signals/byteOrder"),)
_STATUS = (ReplyPlace("results/status <property>"),)
_SCOPE = (ReplyPlace("dbc/attributes/scope <definition>"),)
_WARNING = CppText('    {"warning", IssueSeverity::Warning},\n')
_READ = CppText('field_member(issue, path, "severity", severity_table)')
_LOOKED_UP = CppText(
    'lookup(severity_table, field_string(issue, path, "severity"))'
    + ".value_or(IssueSeverity::Warning)"
)
_LITTLE = CppText('    {"little_endian", ByteOrder::LittleEndian},\n')
_BIG = CppText('    {"big_endian", ByteOrder::BigEndian},\n')
_HOLDS = CppText('    {"holds", Verdict::Holds},\n')
_SCOPE_READ = CppText('field_member(m, path, "scope", attr_scope_table)')
_SCOPE_PARENTHESIZED = CppText('field_member(m, path, "scope", (attr_scope_table))')
_NODE_MSG = CppText('    {"nodeMsg", DbcAttrScope::NodeMsg},\n')
_NODE_SIG = CppText('    {"nodeSig", DbcAttrScope::NodeSig},\n')
_SEVERITY_ENTRIES = CppText('{"warning", IssueSeverity::Warning}, {"x", IssueSeverity::Error},')
_BYTE_ORDER_ENTRIES = CppText(
    '{"little_endian", ByteOrder::LittleEndian}, {"x", ByteOrder::BigEndian},'
)


def _line_of(path: Path, needle: CppText) -> CppLine:
    """Return the line of ``path``'s source ``needle`` starts on."""
    source = path.read_text(encoding="utf-8")
    return CppLine(source[: source.index(needle)].count("\n") + 1)


# Each case: the places it reads, its plant, and what the gate names at each
# place.
_CASES = [
    pytest.param(_SEVERITY, _Plant(CPP_PARSE, _READ, _READ), [], id="severity as written"),
    pytest.param(
        _SEVERITY,
        _Plant(CPP_PARSE, _WARNING, CppText("")),
        [
            Prose("'warning' is in replyText only"),
            Prose("the C++ reader's last arm names 'error', not 'warning'"),
        ],
        id="severity with warning dropped from the table",
    ),
    pytest.param(
        _SEVERITY,
        _Plant(CPP_PARSE, _WARNING, CppText('    {"fatal", IssueSeverity::Error},\n' + _WARNING)),
        [Prose("'fatal' is in the C++ reader only")],
        id="severity with a word added to the table",
    ),
    pytest.param(_BYTE_ORDER, _Plant(CPP_PARSE_DBC, _BIG, _BIG), [], id="byte order as written"),
    pytest.param(
        _BYTE_ORDER,
        _Plant(CPP_PARSE_DBC, _LITTLE, CppText('    {"little_endian", ByteOrder::BigEndian},\n')),
        [
            Prose(
                "cpp/src/json_parse_dbc.cpp:byte_order_table: "
                + "its last entry reads 'big_endian', 'little_endian' alike"
            )
        ],
        id="byte order with little_endian given its last entry's enumerator",
    ),
    pytest.param(
        _BYTE_ORDER,
        _Plant(CPP_PARSE_DBC, CppText(_LITTLE + _BIG), CppText(_BIG + _LITTLE)),
        [Prose("the C++ reader's last arm names 'little_endian', not 'big_endian'")],
        id="byte order with its entries swapped",
    ),
    pytest.param(
        _STATUS,
        _Plant(CPP_PARSE, _HOLDS, CppText('    {"holds", Verdict::Unresolved},\n')),
        [
            Prose(
                "cpp/src/json_parse.cpp:verdict_table: "
                + "its last entry reads 'holds', 'unresolved' alike"
            )
        ],
        id="status with holds given its last entry's enumerator",
    ),
    pytest.param(
        _STATUS,
        _Plant(CPP_PARSE, _HOLDS, CppText('    {"holds", Verdict::Fails},\n')),
        [],
        id="status with holds given the enumerator of an entry before the last",
    ),
    pytest.param(
        _SCOPE, _Plant(CPP_PARSE_DBC, _SCOPE_READ, _SCOPE_READ), [], id="scope as written"
    ),
    pytest.param(
        _SCOPE,
        _Plant(CPP_PARSE_DBC, _NODE_MSG, CppText('    {"nodeMsg", DbcAttrScope::NodeSig},\n')),
        [
            Prose(
                "cpp/src/json_parse_dbc.cpp:attr_scope_table: "
                + "its last entry reads 'nodeMsg', 'nodeSig' alike"
            )
        ],
        id="scope with nodeMsg given its last entry's enumerator",
    ),
    pytest.param(
        _SCOPE,
        _Plant(CPP_PARSE_DBC, CppText(_NODE_MSG + _NODE_SIG), CppText(_NODE_SIG + _NODE_MSG)),
        [Prose("the C++ reader's last arm names 'nodeMsg', not 'nodeSig'")],
        id="scope with its last two entries swapped",
    ),
    pytest.param(
        _SCOPE,
        _Plant(CPP_PARSE_DBC, CppText('    {"network", DbcAttrScope::Network},\n'), CppText("")),
        [Prose("'network' is in replyText only")],
        id="scope with network dropped from the table",
    ),
    pytest.param(
        _SCOPE,
        _Plant(CPP_PARSE_DBC, _SCOPE_READ, _SCOPE_PARENTHESIZED),
        [
            Prose(
                f"cpp/src/json_parse_dbc.cpp:{_line_of(CPP_PARSE_DBC, _SCOPE_READ)}: "
                + f"{CppText(f'.scope = {_SCOPE_PARENTHESIZED},')!r} reaches attr_scope_table "
                + "outside a field_member call; "
                + "cpp/src/json_parse_dbc.cpp:attr_scope_table: no field_member call reads it"
            )
        ],
        id="scope read from its table in parentheses",
    ),
    pytest.param(
        _SEVERITY,
        _Plant(CPP_PARSE, _READ, CppText('field_member(issue, path, "severity", verdict_table)')),
        [Prose("cpp/src/json_parse.cpp:severity_table: no field_member call reads it")],
        id="severity with the table read by no field_member call",
    ),
    pytest.param(
        _SEVERITY,
        _Plant(CPP_PARSE, _WARNING, CppText(f"    {_SEVERITY_ENTRIES}\n")),
        [
            Prose(
                f"cpp/src/json_parse.cpp:severity_table:{_line_of(CPP_PARSE, _WARNING)}: "
                + f"{_SEVERITY_ENTRIES!r} is not one {{word, enumerator}}"
            )
        ],
        id="severity with an entry the gate cannot read",
    ),
    pytest.param(
        _BYTE_ORDER,
        _Plant(CPP_PARSE_DBC, _LITTLE, CppText(f"    {_BYTE_ORDER_ENTRIES}\n")),
        [
            Prose(
                f"cpp/src/json_parse_dbc.cpp:byte_order_table:{_line_of(CPP_PARSE_DBC, _LITTLE)}: "
                + f"{_BYTE_ORDER_ENTRIES!r} is not one {{word, enumerator}}"
            )
        ],
        id="byte order with an entry the gate cannot read",
    ),
]


def _reported(monkeypatch: pytest.MonkeyPatch, plant: _Plant) -> list[Prose]:
    """Return each set the C++ reader cannot read, or else each divergence, with ``plant``."""
    source = plant.path.read_text(encoding="utf-8")
    assert source.count(plant.written) == 1
    text = CppText(source.replace(plant.written, plant.planted))

    def read(each: Path) -> CppText:
        return text if each == plant.path else CppText(each.read_text(encoding="utf-8"))

    monkeypatch.setattr("tools._reply_places_cpp._cpp_source", read)
    agda = AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8"))
    tables = read_reply_tables(agda, (cpp_reader(frozenset()),))
    return tables if isinstance(tables, list) else check_reply_places(tables, frozenset())


def _at(reported: list[Prose], place: ReplyPlace) -> list[Prose]:
    """Return what the gate reported at ``place``, its lead cut."""
    lead = f"reply place {place}: "
    return sorted(Prose(each.removeprefix(lead)) for each in reported if each.startswith(lead))


@pytest.mark.parametrize(("places", "plant", "named"), _CASES)
def test_the_gate_names_at_each_place_what_the_table_reads_amiss(
    monkeypatch: pytest.MonkeyPatch,
    places: tuple[ReplyPlace, ...],
    plant: _Plant,
    named: list[Prose],
) -> None:
    """With ``plant`` in the C++ library, the gate names ``named`` at each place."""
    reported = _reported(monkeypatch, plant)
    for place in places:
        assert _at(reported, place) == named


def test_the_library_as_written_holds_every_row_but_the_bound_kinds() -> None:
    """Read from the library's own files, every place but the bound kinds is in parity."""
    agda = AgdaText(AGDA_REPLY_RANGE.read_text(encoding="utf-8"))
    tables = read_reply_tables(agda, (cpp_reader(frozenset()),))
    assert isinstance(tables, ReplyTables), tables
    bound_kinds = "reply place bound_kind: "
    reported = check_reply_places(tables, frozenset())
    assert [each for each in reported if not each.startswith(bound_kinds)] == []


@pytest.mark.parametrize("place", _SEVERITY)
def test_a_table_reached_outside_a_field_member_call_is_named(
    monkeypatch: pytest.MonkeyPatch, place: ReplyPlace
) -> None:
    """A lookup of the severity table, which would read a last arm, is named at its line."""
    shown = CppText(f"auto const severity = {_LOOKED_UP};")
    reported = _reported(monkeypatch, _Plant(CPP_PARSE, _READ, _LOOKED_UP))
    assert _at(reported, place) == [
        Prose(
            f"cpp/src/json_parse.cpp:{_line_of(CPP_PARSE, _READ)}: {shown!r} reaches "
            + "severity_table outside a field_member call; "
            + "cpp/src/json_parse.cpp:severity_table: no field_member call reads it"
        )
    ]
