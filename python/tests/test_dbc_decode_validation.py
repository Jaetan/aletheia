# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""What the DBC reader decides about the kernel's reply, and what it leaves to the kernel.

``normalize_dbc`` / ``normalize_signal`` / ``parse_extraction_buffer`` refuse a
value of the wrong kind, a key the kernel always writes and the reply lacks and
trailing bytes on the binary extraction buffer; a value's range, a tag's set and
a list's length are the kernel's, proven of every reply, so a number passes as
given and a tag outside its set is read, not refused.  Each refusal sets exactly
one bad field on an otherwise whole reply.  (Real ``formatDBC`` output is
covered end-to-end by ``test_dbc_corpus_parity`` and ``test_format_dbc``.)
"""

from __future__ import annotations

import struct
from typing import TYPE_CHECKING, Literal, NewType, cast, get_args

import pytest
from _dbc_helpers import kernel_signal

from aletheia import ProtocolError
from aletheia._dbc_types import SignalName, empty_dbc_tier2
from aletheia.client._client_bin import parse_extraction_buffer
from aletheia.client._helpers.dbc_normalize import normalize_dbc, normalize_signal
from aletheia.types import JSONValue

if TYPE_CHECKING:
    from aletheia.types import DBCSignalMultiplexed


# The key of a list a DBC reply carries beside its messages, each written by the kernel.
ListKey = NewType("ListKey", str)
_DBC_LISTS = tuple(ListKey(key) for key in empty_dbc_tier2())

# A signal's four numbers, each written by the kernel.
NumericField = Literal["factor", "offset", "minimum", "maximum"]

# The places a reply carries a CAN id beside its messages.
IdPlace = Literal["comment", "attribute", "unresolved"]

# A presence as a reply spells it, in or out of the pair the kernel writes.
WirePresence = NewType("WirePresence", str)

# A list of a DBC reply whose entries carry tags the kernel writes from fixed sets.
TaggedList = Literal["comments", "attributes"]


def _valid_signal() -> dict[str, JSONValue]:
    """Return a whole always-present signal, as the kernel writes one, to mutate."""
    return cast("dict[str, JSONValue]", kernel_signal(SignalName("S")))


def _dbc(**fields: JSONValue) -> dict[str, JSONValue]:
    """Build a whole DBC reply with no messages, any key replaced by ``fields``."""
    return {
        "version": "1.0",
        "messages": [],
        **{key: list[JSONValue]() for key in empty_dbc_tier2()},
        **fields,
    }


def _dbc_with_message(overrides: dict[str, JSONValue]) -> dict[str, JSONValue]:
    """Build a whole DBC reply with one message, field-overridable."""
    return _dbc(
        messages=[
            {
                "id": 0x100,
                "extended": False,
                "name": "M",
                "dlc": 8,
                "sender": "",
                "signals": [_valid_signal()],
                **overrides,
            }
        ]
    )


class TestMessageMetaValidation:
    """A message's CAN id, ``extended`` flag and DLC: the reader holds kinds, the kernel ranges."""

    def test_accepts_well_formed(self) -> None:
        """Decode a well-formed message envelope."""
        assert normalize_dbc(_dbc_with_message({}))["messages"]

    def test_takes_the_id_and_dlc_as_given(self) -> None:
        """No range is decided here: a standard id past 11 bits and a 9-byte DLC pass unchanged."""
        message = normalize_dbc(_dbc_with_message({"id": 0x800, "dlc": 9}))["messages"][0]
        assert (message["id"], message["dlc"], message.get("extended")) == (0x800, 9, False)

    def test_rejects_non_bool_extended(self) -> None:
        """Reject a present-but-non-boolean extended flag (no string coercion)."""
        with pytest.raises(ProtocolError):
            normalize_dbc(_dbc_with_message({"extended": "true"}))

    def test_rejects_a_message_without_extended(self) -> None:
        """The kernel writes ``extended`` at every message, so a reply without it is refused."""
        message: JSONValue = {"id": 0x100, "name": "M", "dlc": 8, "sender": "", "signals": []}
        with pytest.raises(ProtocolError, match="extended"):
            normalize_dbc(_dbc(messages=[message]))


class TestReplyCarriesEveryKey:
    """A key the kernel writes in every DBC reply, if absent, is refused rather than filled in."""

    @pytest.mark.parametrize("field", get_args(NumericField))
    def test_refuses_a_signal_without_a_numeric_field(self, field: NumericField) -> None:
        """A signal missing ``field`` is refused, not decoded without it."""
        sig = _valid_signal()
        del sig[field]
        with pytest.raises(ProtocolError, match=field):
            normalize_signal(sig)

    def test_refuses_a_reply_without_its_version(self) -> None:
        """A reply with no ``version`` is refused, not given an empty one."""
        dbc = _dbc()
        del dbc["version"]
        with pytest.raises(ProtocolError, match="version"):
            normalize_dbc(dbc)

    def test_refuses_a_version_that_is_not_a_string(self) -> None:
        """A ``version`` of another kind is refused, not passed through ``str``."""
        with pytest.raises(ProtocolError, match="version"):
            normalize_dbc(_dbc(version=7))

    @pytest.mark.parametrize("key", _DBC_LISTS)
    def test_refuses_a_reply_without_a_list(self, key: ListKey) -> None:
        """A reply missing a list beside its messages is refused, not given an empty one."""
        dbc = _dbc()
        del dbc[key]
        with pytest.raises(ProtocolError, match=key):
            normalize_dbc(dbc)


def _dbc_with_ids_beside_messages(flagless: IdPlace | None) -> dict[str, JSONValue]:
    """Build a reply with a standard id at a comment, an attribute and a value description target.

    Each id carries ``extended`` false, but the one at ``flagless``, which carries none.
    """

    def at(place: IdPlace, **rest: JSONValue) -> JSONValue:
        if place == flagless:
            return {"id": 0x100, **rest}
        return {"id": 0x100, "extended": False, **rest}

    return _dbc(
        comments=[{"target": at("comment", kind="message"), "text": "m"}],
        attributes=[
            {
                "kind": "assignment",
                "name": "A",
                "target": at("attribute", kind="message"),
                "value": {"kind": "int", "value": 1},
            }
        ],
        unresolvedValueDescs=[
            at("unresolved", signalName="S", entries=[{"value": 0, "description": "Off"}])
        ],
    )


class TestExtendedAtEveryId:
    """``extended`` stays with every CAN id of a reply, true or false, as the kernel wrote it."""

    def test_keeps_a_false_flag_at_every_id_beside_the_messages(self) -> None:
        """A comment, an attribute and a value description target each keep ``extended`` false."""
        decoded = normalize_dbc(_dbc_with_ids_beside_messages(None))
        flags = [c["target"].get("extended") for c in decoded["comments"]]
        flags.extend(
            a["target"].get("extended") for a in decoded["attributes"] if a["kind"] == "assignment"
        )
        flags.extend(u.get("extended") for u in decoded["unresolvedValueDescs"])
        assert flags == [False, False, False]

    @pytest.mark.parametrize("place", get_args(IdPlace))
    def test_refuses_an_id_without_its_flag(self, place: IdPlace) -> None:
        """An id beside a message without ``extended`` is refused, not read as standard."""
        with pytest.raises(ProtocolError, match="extended"):
            normalize_dbc(_dbc_with_ids_beside_messages(place))


class TestSignalBitValidation:
    """Signal ``startBit`` and ``length``: the reader holds the kind, the kernel the range.

    The kernel decided both ranges when it read the DBC and proves them of every
    reply, so the reader takes the numbers as given and refuses only a value
    that is not an integer.
    """

    def test_takes_the_start_bit_and_length_as_given(self) -> None:
        """No range is decided here: the numbers the reply carries pass unchanged."""
        sig = _valid_signal()
        sig["startBit"] = 512
        sig["length"] = 0
        decoded = normalize_signal(sig)
        assert (decoded["startBit"], decoded["length"]) == (512, 0)

    def test_rejects_a_start_bit_that_is_not_an_integer(self) -> None:
        """Reject a startBit of another kind."""
        sig = _valid_signal()
        sig["startBit"] = "7"
        with pytest.raises(ProtocolError, match="startBit' to be int"):
            normalize_signal(sig)

    def test_rejects_a_length_that_is_not_an_integer(self) -> None:
        """Reject a bit length of another kind."""
        sig = _valid_signal()
        sig["length"] = True
        with pytest.raises(ProtocolError, match="length' to be int"):
            normalize_signal(sig)


class TestPresenceValidation:
    """The ``presence`` discriminator: the reader holds the kinds, the kernel the values.

    The kernel writes ``presence`` as always or multiplexed, a multiplexor that is
    not empty and at least one selector value, proven of every reply.
    """

    def test_reads_any_presence_but_always_as_multiplexed(self) -> None:
        """A presence the kernel never writes is read as multiplexed and passed as given."""
        sig = _valid_signal()
        sig["presence"] = "sometimes"
        sig["multiplexor"] = "Mode"
        sig["multiplex_values"] = [0]
        assert dict(normalize_signal(sig))["presence"] == "sometimes"

    @pytest.mark.parametrize("presence", [WirePresence("multiplexed"), WirePresence("sometimes")])
    def test_rejects_a_multiplexor_that_is_not_a_string(self, presence: WirePresence) -> None:
        """Reject a multiplexor of another kind under any presence but always."""
        sig = _valid_signal()
        sig["presence"] = presence
        sig["multiplexor"] = 7
        sig["multiplex_values"] = [0]
        with pytest.raises(ProtocolError, match="'multiplexor' to be str"):
            normalize_signal(sig)

    def test_rejects_missing_presence(self) -> None:
        """Reject a signal with no presence discriminator."""
        sig = _valid_signal()
        del sig["presence"]
        with pytest.raises(ProtocolError, match="'presence' to be str"):
            normalize_signal(sig)

    def test_takes_empty_multiplex_values_as_given(self) -> None:
        """An empty selector list passes as given: the kernel writes at least one value."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        sig["multiplex_values"] = []
        assert dict(normalize_signal(sig))["multiplex_values"] == []

    def test_rejects_multiplexed_missing_values(self) -> None:
        """Reject a multiplexed signal with no multiplex_values key."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        with pytest.raises(ProtocolError, match="'multiplex_values' to be a list"):
            normalize_signal(sig)

    def test_takes_an_empty_multiplexor_as_given(self) -> None:
        """An empty multiplexor name passes as given: the kernel writes it non-empty."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = ""
        sig["multiplex_values"] = [0]
        assert dict(normalize_signal(sig))["multiplexor"] == ""

    def test_takes_a_multiplex_value_past_32_bits_as_given(self) -> None:
        """A selector value's range is the kernel's: one past 32 bits passes unchanged."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        sig["multiplex_values"] = [1 << 32]
        decoded = cast("DBCSignalMultiplexed", normalize_signal(sig))
        assert decoded["multiplex_values"] == [1 << 32]

    def test_rejects_a_multiplex_value_that_is_not_an_integer(self) -> None:
        """Reject a multiplex selector value of another kind."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        sig["multiplex_values"] = [1.5]
        with pytest.raises(ProtocolError, match="multiplex_values' entry to be int"):
            normalize_signal(sig)

    def test_accepts_well_formed_multiplexed(self) -> None:
        """Accept a well-formed multiplexed signal."""
        sig = _valid_signal()
        sig["presence"] = "multiplexed"
        sig["multiplexor"] = "Mode"
        sig["multiplex_values"] = [0, 1]
        assert normalize_signal(sig)["name"] == "S"


class TestTagsReadWithoutTheirSets:
    """A tag's set is the kernel's, proven of every reply: the reader holds the tag's kind.

    A tag outside its set is read, not refused: the last arm of its dispatch
    takes it, and an attribute definition's scope passes as given.
    """

    @pytest.mark.parametrize(
        ("key", "entry", "read"),
        [
            pytest.param(
                "comments",
                {"target": {"kind": "bogus", "envVar": "E"}, "text": "t"},
                {"target": {"kind": "envVar", "envVar": "E"}, "text": "t"},
                id="comment-target",
            ),
            pytest.param(
                "attributes",
                {
                    "kind": "definition",
                    "name": "A",
                    "scope": "bogus",
                    "attrType": {"kind": "string"},
                },
                {
                    "kind": "definition",
                    "name": "A",
                    "scope": "bogus",
                    "attrType": {"kind": "string"},
                },
                id="attribute-scope",
            ),
            pytest.param(
                "attributes",
                {
                    "kind": "definition",
                    "name": "A",
                    "scope": "network",
                    "attrType": {"kind": "bogus", "min": 0, "max": 255},
                },
                {
                    "kind": "definition",
                    "name": "A",
                    "scope": "network",
                    "attrType": {"kind": "hex", "min": 0, "max": 255},
                },
                id="attribute-type",
            ),
            pytest.param(
                "attributes",
                {"kind": "default", "name": "A", "value": {"kind": "bogus", "value": 255}},
                {"kind": "default", "name": "A", "value": {"kind": "hex", "value": 255}},
                id="attribute-value",
            ),
            pytest.param(
                "attributes",
                {
                    "kind": "assignment",
                    "name": "A",
                    "target": {
                        "kind": "bogus",
                        "id": 1,
                        "extended": False,
                        "node": "N",
                        "signal": "S",
                    },
                    "value": {"kind": "int", "value": 1},
                },
                {
                    "kind": "assignment",
                    "name": "A",
                    "target": {
                        "kind": "nodeSig",
                        "id": 1,
                        "extended": False,
                        "node": "N",
                        "signal": "S",
                    },
                    "value": {"kind": "int", "value": 1},
                },
                id="attribute-target",
            ),
            pytest.param(
                "attributes",
                {
                    "kind": "bogus",
                    "name": "A",
                    "target": {"kind": "network"},
                    "value": {"kind": "int", "value": 1},
                },
                {
                    "kind": "assignment",
                    "name": "A",
                    "target": {"kind": "network"},
                    "value": {"kind": "int", "value": 1},
                },
                id="attribute",
            ),
        ],
    )
    def test_reads_a_tag_outside_its_set(
        self, key: TaggedList, entry: JSONValue, read: JSONValue
    ) -> None:
        """A tag the kernel never writes is read by its dispatch's last arm, a scope as given."""
        assert dict(normalize_dbc(_dbc(**{key: [entry]})))[key] == [read]

    def test_rejects_a_scope_that_is_not_a_string(self) -> None:
        """Reject an attribute definition's scope of another kind."""
        definition: JSONValue = {
            "kind": "definition",
            "name": "A",
            "scope": 3,
            "attrType": {"kind": "string"},
        }
        with pytest.raises(ProtocolError, match="'scope' to be str"):
            normalize_dbc(_dbc(attributes=[definition]))


class TestEnvironmentVarTypeDecode:
    """An environment variable's ``varType``: the reader holds the kind, the kernel the range."""

    def test_takes_the_var_type_as_given(self) -> None:
        """No range is decided here: the number the reply carries passes unchanged."""
        decoded = normalize_dbc(
            _dbc(
                environmentVars=[
                    {"name": "V", "varType": 3, "initial": 0, "minimum": 0, "maximum": 1}
                ]
            )
        )
        assert [ev["varType"] for ev in decoded["environmentVars"]] == [3]

    def test_rejects_a_var_type_that_is_not_an_integer(self) -> None:
        """Reject a varType of another kind."""
        with pytest.raises(ProtocolError, match="varType' to be int"):
            normalize_dbc(
                _dbc(
                    environmentVars=[
                        {"name": "V", "varType": True, "initial": 0, "minimum": 0, "maximum": 1}
                    ]
                )
            )


class TestExtractionTrailingBytes:
    """``parse_extraction_buffer`` rejects trailing bytes."""

    def test_accepts_exact_buffer(self) -> None:
        """Accept a buffer consumed exactly (one value, empty offsets table, no tail)."""
        buf = (
            struct.pack("<HHHI", 1, 0, 0, 0)
            + struct.pack("<HBQQQQ", 0, 0, 100, 0, 1, 0)
            + struct.pack("<I", 0)
        )
        assert parse_extraction_buffer(buf, ("Speed",)).values == {"Speed": 100.0}

    def test_rejects_trailing_bytes(self) -> None:
        """Reject a buffer with a trailing byte past the computed layout."""
        buf = (
            struct.pack("<HHHI", 1, 0, 0, 0)
            + struct.pack("<HBQQQQ", 0, 0, 100, 0, 1, 0)
            + struct.pack("<I", 0)
        )
        with pytest.raises(ProtocolError, match="trailing"):
            parse_extraction_buffer(buf + b"\x00", ("Speed",))
