# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Each place of a DBC reply, broken alone, is refused naming its place in the one form.

The DBC reader refuses a value at a place the kernel never writes it as
``reply <path>: expected <what>, got <what came>``: the path the reply proof's,
from ``dbc``, an array's entries keeping the array's path; a rational's
``{numerator, denominator}`` object one place; a deleted key came as
``nothing``.  Every row breaks one place of a reply that reads whole.
"""

from __future__ import annotations

from enum import Enum
from fractions import Fraction
from typing import Final, NewType

import pytest
from _dbc_helpers import kernel_signal

from aletheia import ProtocolError
from aletheia._dbc_types import SignalName
from aletheia.client._helpers.dbc_normalize import normalize_dbc
from aletheia.types import JSONValue, is_str_dict

# A place of a DBC reply spelled as its keys and entry positions joined by dots,
# and one of its steps.
Spot = NewType("Spot", str)
Step = NewType("Step", str)

# The whole text of a reader's refusal.
Refusal = NewType("Refusal", str)


class _Gone(Enum):
    """The key a broken reply lacks."""

    KEY = "deleted"


_GONE: Final = _Gone.KEY


def _always_signal() -> JSONValue:
    """Return an always-present signal with a value description, as the kernel writes one."""
    signal = kernel_signal(SignalName("Mode"))
    assert is_str_dict(signal)
    return {
        **signal,
        "length": 4,
        "maximum": 15,
        "valueDescriptions": [{"value": 0, "description": "Off"}],
    }


def _multiplexed_signal() -> JSONValue:
    """Return a multiplexed signal with rational factor and maximum, as the kernel writes one."""
    always = _always_signal()
    assert is_str_dict(always)
    return {
        **always,
        "name": "Half",
        "startBit": 8,
        "length": 8,
        "factor": {"numerator": 1, "denominator": 2},
        "maximum": {"numerator": 255, "denominator": 2},
        "valueDescriptions": [],
        "presence": "multiplexed",
        "multiplexor": "Mode",
        "multiplex_values": [0],
    }


def _attribute_assignment(target: JSONValue) -> JSONValue:
    """Return an int attribute's assignment to ``target``."""
    return {
        "kind": "assignment",
        "name": "I",
        "target": target,
        "value": {"kind": "int", "value": 2},
    }


def _whole_reply() -> JSONValue:
    """Return a DBC reply holding every place the reader reads, each as the kernel writes it."""
    message_id = {"extended": False, "id": 256}
    return {
        "version": "1.0",
        "messages": [
            {
                **message_id,
                "name": "M",
                "dlc": 8,
                "sender": "ECU",
                "senders": [],
                "signals": [_always_signal(), _multiplexed_signal()],
            }
        ],
        "signalGroups": [{"name": "G", "signals": ["Mode"]}],
        "environmentVars": [{"name": "V", "varType": 0, "initial": 0, "minimum": 0, "maximum": 1}],
        "valueTables": [{"name": "T", "entries": [{"value": 0, "description": "Off"}]}],
        "nodes": [{"name": "ECU"}],
        "comments": [
            {"target": {"kind": "network"}, "text": "n"},
            {"target": {"kind": "node", "node": "ECU"}, "text": "e"},
            {"target": {"kind": "message", **message_id}, "text": "m"},
            {"target": {"kind": "signal", **message_id, "signal": "Mode"}, "text": "s"},
            {"target": {"kind": "envVar", "envVar": "V"}, "text": "v"},
        ],
        "attributes": [
            {
                "kind": "definition",
                "name": "I",
                "scope": "network",
                "attrType": {"kind": "int", "min": 0, "max": 10},
            },
            {
                "kind": "definition",
                "name": "F",
                "scope": "node",
                "attrType": {"kind": "float", "min": 0, "max": {"numerator": 1, "denominator": 2}},
            },
            {
                "kind": "definition",
                "name": "E",
                "scope": "message",
                "attrType": {"kind": "enum", "values": ["Low", "High"]},
            },
            {
                "kind": "definition",
                "name": "H",
                "scope": "signal",
                "attrType": {"kind": "hex", "min": 0, "max": 255},
            },
            {"kind": "definition", "name": "S", "scope": "envVar", "attrType": {"kind": "string"}},
            {"kind": "default", "name": "I", "value": {"kind": "int", "value": 1}},
            {
                "kind": "default",
                "name": "F",
                "value": {"kind": "float", "value": {"numerator": 1, "denominator": 4}},
            },
            {"kind": "default", "name": "S", "value": {"kind": "string", "value": "x"}},
            {"kind": "default", "name": "E", "value": {"kind": "enum", "value": 0}},
            {"kind": "default", "name": "H", "value": {"kind": "hex", "value": 255}},
            _attribute_assignment({"kind": "network"}),
            _attribute_assignment({"kind": "node", "node": "ECU"}),
            _attribute_assignment({"kind": "message", **message_id}),
            _attribute_assignment({"kind": "signal", **message_id, "signal": "Mode"}),
            _attribute_assignment({"kind": "envVar", "envVar": "V"}),
            _attribute_assignment({"kind": "nodeMsg", **message_id, "node": "ECU"}),
            _attribute_assignment(
                {"kind": "nodeSig", **message_id, "node": "ECU", "signal": "Mode"}
            ),
        ],
        "unresolvedValueDescs": [
            {
                "extended": False,
                "id": 999,
                "signalName": "Ghost",
                "entries": [{"value": 0, "description": "Zero"}],
            }
        ],
    }


def _child(value: JSONValue, step: Step) -> JSONValue:
    """Read one step down: an array's entry at a position, an object's value at a key."""
    if isinstance(value, list):
        return value[int(step)]
    assert isinstance(value, dict), value
    return value[step]


def _broken(spot: Spot, replacement: JSONValue | _Gone) -> JSONValue:
    """Return the whole reply with the value at ``spot`` replaced, or its key deleted."""
    reply = _whole_reply()
    *outer, last = (Step(step) for step in spot.split("."))
    holder = reply
    for step in outer:
        holder = _child(holder, step)
    if isinstance(holder, list):
        assert not isinstance(replacement, _Gone), spot
        holder[int(last)] = replacement
    else:
        assert isinstance(holder, dict), spot
        if isinstance(replacement, _Gone):
            del holder[last]
        else:
            holder[last] = replacement
    return reply


# One broken place per row: where, what replaces it, and the refusal naming it.
_BROKEN_PLACES: Final = (
    ("messages", _GONE, "reply dbc/messages: expected array, got nothing"),
    ("messages", 0, "reply dbc/messages: expected array, got number"),
    ("messages.0", 0, "reply dbc/messages: expected object, got number"),
    ("messages.0.id", _GONE, "reply dbc/messages/id: expected number, got nothing"),
    ("messages.0.id", "x", "reply dbc/messages/id: expected number, got string"),
    ("messages.0.extended", 0, "reply dbc/messages/extended: expected boolean, got number"),
    ("messages.0.dlc", "x", "reply dbc/messages/dlc: expected number, got string"),
    ("messages.0.name", _GONE, "reply dbc/messages/name: expected string, got nothing"),
    ("messages.0.sender", 0, "reply dbc/messages/sender: expected string, got number"),
    ("messages.0.senders", _GONE, "reply dbc/messages/senders: expected array, got nothing"),
    ("messages.0.senders", [0], "reply dbc/messages/senders: expected string, got number"),
    ("messages.0.signals", _GONE, "reply dbc/messages/signals: expected array, got nothing"),
    ("messages.0.signals.0", 0, "reply dbc/messages/signals: expected object, got number"),
    (
        "messages.0.signals.0.startBit",
        _GONE,
        "reply dbc/messages/signals/startBit: expected number, got nothing",
    ),
    (
        "messages.0.signals.0.length",
        "x",
        "reply dbc/messages/signals/length: expected number, got string",
    ),
    (
        "messages.0.signals.0.byteOrder",
        _GONE,
        "reply dbc/messages/signals/byteOrder: expected string, got nothing",
    ),
    (
        "messages.0.signals.0.byteOrder",
        0,
        "reply dbc/messages/signals/byteOrder: expected string, got number",
    ),
    (
        "messages.0.signals.0.name",
        0,
        "reply dbc/messages/signals/name: expected string, got number",
    ),
    (
        "messages.0.signals.0.signed",
        _GONE,
        "reply dbc/messages/signals/signed: expected boolean, got nothing",
    ),
    (
        "messages.0.signals.0.unit",
        0,
        "reply dbc/messages/signals/unit: expected string, got number",
    ),
    (
        "messages.0.signals.0.receivers",
        "x",
        "reply dbc/messages/signals/receivers: expected array, got string",
    ),
    (
        "messages.0.signals.0.receivers",
        [0],
        "reply dbc/messages/signals/receivers: expected string, got number",
    ),
    (
        "messages.0.signals.0.factor",
        "x",
        "reply dbc/messages/signals/factor: expected a rational, got string",
    ),
    (
        "messages.0.signals.1.factor.numerator",
        "x",
        "reply dbc/messages/signals/factor: expected a rational, got object",
    ),
    (
        "messages.0.signals.0.offset",
        None,
        "reply dbc/messages/signals/offset: expected a rational, got null",
    ),
    (
        "messages.0.signals.0.minimum",
        False,
        "reply dbc/messages/signals/minimum: expected a rational, got boolean",
    ),
    (
        "messages.0.signals.1.maximum",
        "x",
        "reply dbc/messages/signals/maximum: expected a rational, got string",
    ),
    (
        "messages.0.signals.0.valueDescriptions",
        _GONE,
        "reply dbc/messages/signals/valueDescriptions: expected array, got nothing",
    ),
    (
        "messages.0.signals.0.valueDescriptions.0",
        0,
        "reply dbc/messages/signals/valueDescriptions: expected object, got number",
    ),
    (
        "messages.0.signals.0.valueDescriptions.0.value",
        "x",
        "reply dbc/messages/signals/valueDescriptions/value: expected number, got string",
    ),
    (
        "messages.0.signals.0.valueDescriptions.0.description",
        _GONE,
        "reply dbc/messages/signals/valueDescriptions/description: expected string, got nothing",
    ),
    (
        "messages.0.signals.0.presence",
        0,
        "reply dbc/messages/signals/presence: expected string, got number",
    ),
    (
        "messages.0.signals.1.multiplexor",
        _GONE,
        "reply dbc/messages/signals/multiplexor: expected string, got nothing",
    ),
    (
        "messages.0.signals.1.multiplex_values",
        0,
        "reply dbc/messages/signals/multiplex_values: expected array, got number",
    ),
    (
        "messages.0.signals.1.multiplex_values.0",
        "x",
        "reply dbc/messages/signals/multiplex_values: expected number, got string",
    ),
    ("signalGroups", 0, "reply dbc/signalGroups: expected array, got number"),
    ("signalGroups.0", "x", "reply dbc/signalGroups: expected object, got string"),
    ("signalGroups.0.name", _GONE, "reply dbc/signalGroups/name: expected string, got nothing"),
    (
        "signalGroups.0.signals",
        _GONE,
        "reply dbc/signalGroups/signals: expected array, got nothing",
    ),
    ("signalGroups.0.signals.0", 0, "reply dbc/signalGroups/signals: expected string, got number"),
    ("environmentVars.0", 0, "reply dbc/environmentVars: expected object, got number"),
    ("environmentVars.0.name", 0, "reply dbc/environmentVars/name: expected string, got number"),
    (
        "environmentVars.0.varType",
        _GONE,
        "reply dbc/environmentVars/varType: expected number, got nothing",
    ),
    (
        "environmentVars.0.initial",
        _GONE,
        "reply dbc/environmentVars/initial: expected a rational, got nothing",
    ),
    (
        "environmentVars.0.minimum",
        "x",
        "reply dbc/environmentVars/minimum: expected a rational, got string",
    ),
    (
        "environmentVars.0.maximum",
        None,
        "reply dbc/environmentVars/maximum: expected a rational, got null",
    ),
    ("valueTables.0", 0, "reply dbc/valueTables: expected object, got number"),
    ("valueTables.0.name", _GONE, "reply dbc/valueTables/name: expected string, got nothing"),
    ("valueTables.0.entries", 0, "reply dbc/valueTables/entries: expected array, got number"),
    ("valueTables.0.entries.0", "x", "reply dbc/valueTables/entries: expected object, got string"),
    (
        "valueTables.0.entries.0.value",
        "x",
        "reply dbc/valueTables/entries/value: expected number, got string",
    ),
    (
        "valueTables.0.entries.0.description",
        0,
        "reply dbc/valueTables/entries/description: expected string, got number",
    ),
    ("nodes.0", 0, "reply dbc/nodes: expected object, got number"),
    ("nodes.0.name", _GONE, "reply dbc/nodes/name: expected string, got nothing"),
    ("comments.0", 0, "reply dbc/comments: expected object, got number"),
    ("comments.0.target", _GONE, "reply dbc/comments/target: expected object, got nothing"),
    ("comments.0.text", 0, "reply dbc/comments/text: expected string, got number"),
    ("comments.0.target.kind", 0, "reply dbc/comments/target/kind: expected string, got number"),
    (
        "comments.1.target.node",
        _GONE,
        "reply dbc/comments/target/node: expected string, got nothing",
    ),
    ("comments.2.target.id", "x", "reply dbc/comments/target/id: expected number, got string"),
    (
        "comments.2.target.extended",
        0,
        "reply dbc/comments/target/extended: expected boolean, got number",
    ),
    ("comments.3.target.id", _GONE, "reply dbc/comments/target/id: expected number, got nothing"),
    (
        "comments.3.target.signal",
        _GONE,
        "reply dbc/comments/target/signal: expected string, got nothing",
    ),
    (
        "comments.4.target.envVar",
        0,
        "reply dbc/comments/target/envVar: expected string, got number",
    ),
    ("attributes.0", 0, "reply dbc/attributes: expected object, got number"),
    ("attributes.0.kind", _GONE, "reply dbc/attributes/kind: expected string, got nothing"),
    ("attributes.0.name", 0, "reply dbc/attributes/name: expected string, got number"),
    ("attributes.0.scope", _GONE, "reply dbc/attributes/scope: expected string, got nothing"),
    ("attributes.0.attrType", 0, "reply dbc/attributes/attrType: expected object, got number"),
    (
        "attributes.0.attrType.kind",
        _GONE,
        "reply dbc/attributes/attrType/kind: expected string, got nothing",
    ),
    (
        "attributes.0.attrType.min",
        "x",
        "reply dbc/attributes/attrType/min: expected number, got string",
    ),
    (
        "attributes.0.attrType.max",
        _GONE,
        "reply dbc/attributes/attrType/max: expected number, got nothing",
    ),
    (
        "attributes.1.attrType.min",
        _GONE,
        "reply dbc/attributes/attrType/min: expected a rational, got nothing",
    ),
    (
        "attributes.1.attrType.max",
        "x",
        "reply dbc/attributes/attrType/max: expected a rational, got string",
    ),
    (
        "attributes.2.attrType.values",
        _GONE,
        "reply dbc/attributes/attrType/values: expected array, got nothing",
    ),
    (
        "attributes.2.attrType.values.0",
        0,
        "reply dbc/attributes/attrType/values: expected string, got number",
    ),
    (
        "attributes.3.attrType.min",
        _GONE,
        "reply dbc/attributes/attrType/min: expected number, got nothing",
    ),
    (
        "attributes.3.attrType.max",
        "x",
        "reply dbc/attributes/attrType/max: expected number, got string",
    ),
    ("attributes.5.value", _GONE, "reply dbc/attributes/value: expected object, got nothing"),
    ("attributes.5.value.kind", 0, "reply dbc/attributes/value/kind: expected string, got number"),
    (
        "attributes.5.value.value",
        "x",
        "reply dbc/attributes/value/value: expected number, got string",
    ),
    (
        "attributes.6.value.value",
        _GONE,
        "reply dbc/attributes/value/value: expected a rational, got nothing",
    ),
    (
        "attributes.6.value.value",
        "x",
        "reply dbc/attributes/value/value: expected a rational, got string",
    ),
    (
        "attributes.7.value.value",
        0,
        "reply dbc/attributes/value/value: expected string, got number",
    ),
    (
        "attributes.8.value.value",
        "x",
        "reply dbc/attributes/value/value: expected number, got string",
    ),
    (
        "attributes.9.value.value",
        _GONE,
        "reply dbc/attributes/value/value: expected number, got nothing",
    ),
    ("attributes.10.target", 0, "reply dbc/attributes/target: expected object, got number"),
    ("attributes.10.value", _GONE, "reply dbc/attributes/value: expected object, got nothing"),
    (
        "attributes.10.target.kind",
        _GONE,
        "reply dbc/attributes/target/kind: expected string, got nothing",
    ),
    (
        "attributes.11.target.node",
        0,
        "reply dbc/attributes/target/node: expected string, got number",
    ),
    (
        "attributes.12.target.id",
        _GONE,
        "reply dbc/attributes/target/id: expected number, got nothing",
    ),
    (
        "attributes.12.target.extended",
        0,
        "reply dbc/attributes/target/extended: expected boolean, got number",
    ),
    (
        "attributes.13.target.signal",
        _GONE,
        "reply dbc/attributes/target/signal: expected string, got nothing",
    ),
    (
        "attributes.14.target.envVar",
        _GONE,
        "reply dbc/attributes/target/envVar: expected string, got nothing",
    ),
    (
        "attributes.15.target.node",
        _GONE,
        "reply dbc/attributes/target/node: expected string, got nothing",
    ),
    (
        "attributes.16.target.signal",
        0,
        "reply dbc/attributes/target/signal: expected string, got number",
    ),
    ("unresolvedValueDescs.0", 0, "reply dbc/unresolvedValueDescs: expected object, got number"),
    (
        "unresolvedValueDescs.0.id",
        "x",
        "reply dbc/unresolvedValueDescs/id: expected number, got string",
    ),
    (
        "unresolvedValueDescs.0.signalName",
        _GONE,
        "reply dbc/unresolvedValueDescs/signalName: expected string, got nothing",
    ),
    (
        "unresolvedValueDescs.0.extended",
        0,
        "reply dbc/unresolvedValueDescs/extended: expected boolean, got number",
    ),
    (
        "unresolvedValueDescs.0.entries",
        _GONE,
        "reply dbc/unresolvedValueDescs/entries: expected array, got nothing",
    ),
    (
        "unresolvedValueDescs.0.entries.0",
        0,
        "reply dbc/unresolvedValueDescs/entries: expected object, got number",
    ),
    (
        "unresolvedValueDescs.0.entries.0.value",
        _GONE,
        "reply dbc/unresolvedValueDescs/entries/value: expected number, got nothing",
    ),
    (
        "unresolvedValueDescs.0.entries.0.description",
        0,
        "reply dbc/unresolvedValueDescs/entries/description: expected string, got number",
    ),
)


class TestEachPlaceRefusedInTheOneForm:
    """Each place of a DBC reply, broken alone, is refused by its path, kind and arrival."""

    def test_reads_the_whole_reply(self) -> None:
        """The reply every row breaks reads whole, a rational as its fraction."""
        whole = _whole_reply()
        assert is_str_dict(whole)
        signal = normalize_dbc(whole)["messages"][0]["signals"][1]
        assert (signal["factor"], signal["maximum"]) == (Fraction(1, 2), Fraction(255, 2))

    @pytest.mark.parametrize(
        ("spot", "replacement", "text"),
        _BROKEN_PLACES,
        ids=[
            f"{spot}-{'deleted' if new is _GONE else 'retyped'}" for spot, new, _ in _BROKEN_PLACES
        ],
    )
    def test_refuses_a_broken_place(
        self, spot: Spot, replacement: JSONValue | _Gone, text: Refusal
    ) -> None:
        """The reader refuses the place ``spot`` broken as ``replacement`` says, in the one form."""
        broken = _broken(spot, replacement)
        assert is_str_dict(broken)
        with pytest.raises(ProtocolError) as refusal:
            normalize_dbc(broken)
        assert str(refusal.value) == text
