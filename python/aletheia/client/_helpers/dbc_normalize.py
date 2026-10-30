# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Outbound (TypedDict → wire JSON) and inbound (Agda formatDBC → DBCDefinition) normalisation."""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, LiteralString, cast

from aletheia.client._helpers.rational import is_pure_int, reject_inexact
from aletheia.client._helpers.reply_shape import (
    A_RATIONAL,
    ARRAY,
    BOOLEAN,
    NUMBER,
    OBJECT,
    STRING,
    ReplyPath,
    at,
    came,
    came_as,
    read_rational,
    reply_refusal,
)
from aletheia.types import (
    AttrScope,
    DBCAttribute,
    DBCAttrTarget,
    DBCAttrType,
    DBCAttrValue,
    DBCComment,
    DBCCommentTarget,
    DBCDefinition,
    DBCEnvironmentVar,
    DBCMessage,
    DBCNode,
    DBCRawValueDesc,
    DBCSignal,
    DBCSignalGroup,
    DBCValueEntry,
    DBCValueTable,
    DBCVarType,
    is_str_dict,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping
    from fractions import Fraction

    from aletheia.client._helpers.reply_shape import ReplyFields
    from aletheia.types import JSONValue

# A signal's rationals.
_NUMERIC_SIGNAL_FIELDS: Final = ("factor", "offset", "minimum", "maximum")

# An environment variable's rationals.
_NUMERIC_ENV_VAR_FIELDS: Final = ("initial", "minimum", "maximum")

# The DBC object of a reply, and where every reply carrying one writes a signal.
_DBC: Final = ReplyPath("dbc")
_SIGNALS: Final = at(at(_DBC, "messages"), "signals")


# Outgoing-DBC normalization: C++/Go always emit these list keys (their
# structs hold non-optional list fields), while Python's TypedDict uses
# ``NotRequired`` so callers may omit them.  Filling in `[]` defaults
# before serialization aligns Python's wire shape with C++/Go — every
# binding's FFI dispatcher sees the same JSON envelope.
_DBC_TIER2_LIST_KEYS = (
    "signalGroups",
    "environmentVars",
    "valueTables",
    "nodes",
    "comments",
    "attributes",
    "unresolvedValueDescs",
)


def _normalize_signal_for_wire(sig: dict[str, object]) -> dict[str, object]:
    """Ensure NotRequired signal list fields are present + reject an inexact rational field.

    The outbound twin of ``normalize_signal``'s inbound ``read_rational``:
    each ℚ-valued metadata field (factor/offset/minimum/maximum) must be an exact
    ``int`` or ``Fraction`` — never a ``float`` (which the kernel would silently
    absorb as a wrong rational) nor a ``bool`` (``reject_inexact`` rejects both).
    Integer fields (startBit/length/multiplex_values) are left to the kernel's own
    typed validation.
    """
    name = sig.get("name", "?")
    for field in _NUMERIC_SIGNAL_FIELDS:
        if field in sig:
            reject_inexact(sig[field], f"signal {name!r} {field}")
    return {
        **sig,
        "receivers": sig.get("receivers", []),
        "valueDescriptions": sig.get("valueDescriptions", []),
    }


def _normalize_message_for_wire(msg: dict[str, object]) -> dict[str, object]:
    """Ensure NotRequired message list fields are present in outgoing JSON."""
    signals = cast("list[dict[str, object]]", msg.get("signals", []))
    return {
        **msg,
        "senders": msg.get("senders", []),
        "signals": [_normalize_signal_for_wire(s) for s in signals],
    }


def _reject_env_var_inexact(env_vars: object) -> None:
    """Reject a float or bool at an env-var rational field (initial/minimum/maximum).

    The outbound twin of ``_normalize_environment_var``'s inbound
    ``read_rational`` (via ``reject_inexact``, which rejects both a
    ``float`` and a ``bool``); ``varType`` is a 0/1/2 integer the kernel validates.
    """
    if not isinstance(env_vars, list):
        return
    for ev in cast("list[object]", env_vars):
        if not isinstance(ev, dict):
            continue
        ev_dict = cast("dict[str, object]", ev)
        name = ev_dict.get("name", "?")
        for field in _NUMERIC_ENV_VAR_FIELDS:
            if field in ev_dict:
                reject_inexact(ev_dict[field], f"environment variable {name!r} {field}")


def _reject_attribute_inexact(attributes: object) -> None:
    """Reject a float or bool at a float-kind attribute's rational field (min/max/value).

    Only ``FLOAT`` attribute *definitions* (``attrType.kind == "float"``) and float
    attribute *values* (``value.kind == "float"``) carry ℚ — the outbound twin of
    ``_normalize_attr_type`` / ``_normalize_attr_value`` (via ``reject_inexact``,
    which rejects both a ``float`` and a ``bool``).  INT/HEX bounds and INT/ENUM/HEX
    values are integers the kernel validates.
    """
    if not isinstance(attributes, list):
        return
    for attr in cast("list[object]", attributes):
        if not isinstance(attr, dict):
            continue
        attr_dict = cast("dict[str, object]", attr)
        name = attr_dict.get("name", "?")
        attr_type = attr_dict.get("attrType")
        if isinstance(attr_type, dict):
            type_dict = cast("dict[str, object]", attr_type)
            if type_dict.get("kind") == "float":
                for field in ("min", "max"):
                    if field in type_dict:
                        reject_inexact(type_dict[field], f"attribute {name!r} type {field}")
        value = attr_dict.get("value")
        if isinstance(value, dict):
            value_dict = cast("dict[str, object]", value)
            if value_dict.get("kind") == "float" and "value" in value_dict:
                reject_inexact(value_dict["value"], f"attribute {name!r} value")


def normalize_dbc_for_wire(dbc: DBCDefinition) -> DBCDefinition:
    """Pad an outgoing ``DBCDefinition`` with empty defaults for absent list fields.

    C++/Go always emit the optional Tier-2 list keys (``nodes``, ``comments``,
    …) and the per-message ``senders`` / per-signal ``receivers`` /
    ``valueDescriptions`` because their language-level structs hold
    non-optional list fields.  Python's TypedDict ``NotRequired`` lets
    callers omit them.  This helper aligns Python's outgoing wire shape
    with C++/Go so the JSON envelope reaching the FFI dispatcher is
    identical regardless of which binding constructed the request.

    The float principle (the outbound twin of the inbound ``read_rational``):
    every ℚ-valued metadata field a caller may set in code — signal
    ``factor``/``offset``/``minimum``/``maximum`` (checked in
    ``_normalize_signal_for_wire``), env-var ``initial``/``minimum``/``maximum``,
    and float-kind attribute ``min``/``max``/``value`` — must be an exact ``int``
    or ``Fraction``, never a ``float`` (which the kernel would silently absorb as a
    wrong rational) nor a ``bool`` (``reject_inexact`` rejects both).  Integer wire
    fields (``multiplex_values``, ``startBit``, ``id``…) are left to the kernel's
    own typed validation, which rejects a non-integer there loudly rather than
    silently.
    """
    _reject_env_var_inexact(dbc.get("environmentVars"))
    _reject_attribute_inexact(dbc.get("attributes"))
    messages = cast("list[dict[str, object]]", dbc.get("messages", []))
    result: dict[str, object] = {
        **dbc,
        "messages": [_normalize_message_for_wire(m) for m in messages],
    }
    for key in _DBC_TIER2_LIST_KEYS:
        if key not in result:
            result[key] = []
    return cast("DBCDefinition", result)


# DEFERRED:
# Finding: `normalize_signal` is exposed publicly (no underscore prefix) but
#   only called by this module's internal helpers + tests.
# Why: Mechanical underscore-prefix + import update; same shape as the
#   wider boundary-naming sweep (see DEFERRED block in
#   `aletheia/_loader_utils.py`).
# Revisit when: Co-decided with the _loader_utils.py deferral.
def normalize_signal(raw_sig: Mapping[str, JSONValue], path: ReplyPath = _SIGNALS) -> DBCSignal:
    """Read a signal at ``path``, ``dbc/messages/signals`` in every reply.

    Every field the kernel writes is read by kind. Their ranges and tags are the
    kernel's, decided when it read the DBC and proven of every reply.
    """
    sig: dict[str, object] = {
        **raw_sig,
        "name": _string(raw_sig, path, "name"),
        "startBit": _whole(raw_sig, path, "startBit"),
        "length": _whole(raw_sig, path, "length"),
        "byteOrder": _string(raw_sig, path, "byteOrder"),
        "signed": _boolean(raw_sig, path, "signed"),
        **{field: _rational(raw_sig, path, field) for field in _NUMERIC_SIGNAL_FIELDS},
        "unit": _string(raw_sig, path, "unit"),
        "receivers": _strings(raw_sig, path, "receivers"),
        "valueDescriptions": _normalize_list(raw_sig, path, "valueDescriptions", _value_entry),
    }
    _check_presence(raw_sig, path)
    return cast("DBCSignal", sig)


def _check_presence(raw: ReplyFields, path: ReplyPath) -> None:
    """Refuse a ``presence`` or a multiplexed signal's field that is not of its kind.

    The kernel writes ``presence`` as ``"always"`` or ``"multiplexed"``, a
    multiplexor that is not empty and at least one selector value in range, all
    proven of every reply, so the reader holds only the kinds and reads any
    ``presence`` but ``"always"`` as multiplexed.
    """
    if _string(raw, path, "presence") == "always":
        return
    _ = _string(raw, path, "multiplexor")
    place = at(path, "multiplex_values")
    for entry in _array(raw, path, "multiplex_values"):
        if not is_pure_int(entry):
            raise reply_refusal(place, NUMBER, came_as(entry))


def _normalize_message(raw: Mapping[str, JSONValue], path: ReplyPath) -> DBCMessage:
    """Read one message, every field the kernel writes by kind.

    The id's and the DLC's ranges are the kernel's, decided when it read the DBC
    and proven of every reply; the kernel writes ``extended`` at every message.
    """
    place = at(path, "signals")
    signals: list[DBCSignal] = []
    for entry in _array(raw, path, "signals"):
        if not is_str_dict(entry):
            raise reply_refusal(place, OBJECT, came_as(entry))
        signals.append(normalize_signal(entry, place))
    message: dict[str, object] = {
        **raw,
        "name": _string(raw, path, "name"),
        "signals": signals,
        "id": _whole(raw, path, "id"),
        "extended": _boolean(raw, path, "extended"),
        "dlc": _whole(raw, path, "dlc"),
        "sender": _string(raw, path, "sender"),
        "senders": _strings(raw, path, "senders"),
    }
    return cast("DBCMessage", message)


def _normalize_messages(raw: ReplyFields, path: ReplyPath) -> list[DBCMessage]:
    """Read the ``messages`` array of the DBC at ``path``, each entry an object."""
    place = at(path, "messages")
    messages: list[DBCMessage] = []
    for entry in _array(raw, path, "messages"):
        if not is_str_dict(entry):
            raise reply_refusal(place, OBJECT, came_as(entry))
        messages.append(_normalize_message(entry, place))
    return messages


def _normalize_signal_group(raw: ReplyFields, path: ReplyPath) -> DBCSignalGroup:
    """Read one ``signalGroups`` entry: its name and its member signals' names."""
    return {"name": _string(raw, path, "name"), "signals": _strings(raw, path, "signals")}


def _normalize_environment_var(raw: ReplyFields, path: ReplyPath) -> DBCEnvironmentVar:
    """Read one ``environmentVars`` entry.

    The ``varType`` range is the kernel's, decided when it read the DBC and
    proven of every reply, so the reader holds only its kind.
    """
    return {
        "name": _string(raw, path, "name"),
        "varType": _var_type(raw, path),
        "initial": _rational(raw, path, "initial"),
        "minimum": _rational(raw, path, "minimum"),
        "maximum": _rational(raw, path, "maximum"),
    }


def _var_type(raw: ReplyFields, path: ReplyPath) -> DBCVarType:
    """Read an environment variable's ``varType`` as the ``DBCVarType`` it is proven to be."""
    return cast("DBCVarType", _whole(raw, path, "varType"))


def _value_entry(raw: ReplyFields, path: ReplyPath) -> DBCValueEntry:
    """Read one value description: a key and its text.

    A key is signed, its range the kernel's, so the reader holds only the kind.
    """
    return {"value": _whole(raw, path, "value"), "description": _string(raw, path, "description")}


def _normalize_value_table(raw: ReplyFields, path: ReplyPath) -> DBCValueTable:
    """Read one ``valueTables`` entry: its name and its value descriptions."""
    return {
        "name": _string(raw, path, "name"),
        "entries": _normalize_list(raw, path, "entries", _value_entry),
    }


def _normalize_raw_value_desc(raw: ReplyFields, path: ReplyPath) -> DBCRawValueDesc:
    """Read one ``unresolvedValueDescs`` entry, its CAN id as a message's.

    The wire shape is ``{id, extended, signalName, entries}``.
    """
    return {
        "id": _whole(raw, path, "id"),
        "signalName": _string(raw, path, "signalName"),
        "entries": _normalize_list(raw, path, "entries", _value_entry),
        "extended": _boolean(raw, path, "extended"),
    }


# ----------------------------------------------------------------------------
# Tier 2 metadata normalisation (nodes / comments / attributes)
#
# Each tag below (a comment target's kind, an attribute's, its type's, value's
# and target's kind, a definition's scope) is one of a fixed set the kernel
# proves of every reply, so a reader holds only the tag's kind: a dispatch's
# last arm reads every tag the arms before it do not name, and a scope is cast.
# ----------------------------------------------------------------------------


def _normalize_node(raw: ReplyFields, path: ReplyPath) -> DBCNode:
    return {"name": _string(raw, path, "name")}


def _normalize_comment_target(raw: ReplyFields, path: ReplyPath) -> DBCCommentTarget:
    kind = _string(raw, path, "kind")
    if kind == "network":
        return {"kind": "network"}
    if kind == "node":
        return {"kind": "node", "node": _string(raw, path, "node")}
    if kind == "message":
        return {
            "kind": "message",
            "id": _whole(raw, path, "id"),
            "extended": _boolean(raw, path, "extended"),
        }
    if kind == "signal":
        return {
            "kind": "signal",
            "id": _whole(raw, path, "id"),
            "signal": _string(raw, path, "signal"),
            "extended": _boolean(raw, path, "extended"),
        }
    return {"kind": "envVar", "envVar": _string(raw, path, "envVar")}


def _normalize_comment(raw: ReplyFields, path: ReplyPath) -> DBCComment:
    return {
        "target": _read_object(raw, path, "target", _normalize_comment_target),
        "text": _string(raw, path, "text"),
    }


def _attr_scope(raw: ReplyFields, path: ReplyPath) -> AttrScope:
    """Read an attribute definition's ``scope`` as the ``AttrScope`` it is proven to be."""
    return cast("AttrScope", _string(raw, path, "scope"))


def _normalize_attr_type(raw: ReplyFields, path: ReplyPath) -> DBCAttrType:
    kind = _string(raw, path, "kind")
    if kind == "int":
        return {"kind": "int", "min": _whole(raw, path, "min"), "max": _whole(raw, path, "max")}
    if kind == "float":
        return {
            "kind": "float",
            "min": _rational(raw, path, "min"),
            "max": _rational(raw, path, "max"),
        }
    if kind == "string":
        return {"kind": "string"}
    if kind == "enum":
        return {"kind": "enum", "values": _strings(raw, path, "values")}
    return {"kind": "hex", "min": _whole(raw, path, "min"), "max": _whole(raw, path, "max")}


def _normalize_attr_value(raw: ReplyFields, path: ReplyPath) -> DBCAttrValue:
    kind = _string(raw, path, "kind")
    if kind == "int":
        return {"kind": "int", "value": _whole(raw, path, "value")}
    if kind == "float":
        return {"kind": "float", "value": _rational(raw, path, "value")}
    if kind == "string":
        return {"kind": "string", "value": _string(raw, path, "value")}
    if kind == "enum":
        return {"kind": "enum", "value": _whole(raw, path, "value")}
    return {"kind": "hex", "value": _whole(raw, path, "value")}


def _normalize_attr_target_at_id(kind: str, raw: ReplyFields, path: ReplyPath) -> DBCAttrTarget:
    """Read an attribute target that carries a CAN id, ``nodeSig`` its last arm."""
    can_id = _whole(raw, path, "id")
    extended = _boolean(raw, path, "extended")
    if kind == "message":
        return {"kind": "message", "id": can_id, "extended": extended}
    if kind == "signal":
        signal = _string(raw, path, "signal")
        return {"kind": "signal", "id": can_id, "extended": extended, "signal": signal}
    node = _string(raw, path, "node")
    if kind == "nodeMsg":
        return {"kind": "nodeMsg", "id": can_id, "extended": extended, "node": node}
    signal = _string(raw, path, "signal")
    return {"kind": "nodeSig", "id": can_id, "extended": extended, "node": node, "signal": signal}


def _normalize_attr_target(raw: ReplyFields, path: ReplyPath) -> DBCAttrTarget:
    kind = _string(raw, path, "kind")
    if kind == "network":
        return {"kind": "network"}
    if kind == "node":
        return {"kind": "node", "node": _string(raw, path, "node")}
    if kind == "envVar":
        return {"kind": "envVar", "envVar": _string(raw, path, "envVar")}
    return _normalize_attr_target_at_id(kind, raw, path)


def _normalize_attribute(raw: ReplyFields, path: ReplyPath) -> DBCAttribute:
    kind = _string(raw, path, "kind")
    name = _string(raw, path, "name")
    if kind == "definition":
        return {
            "kind": "definition",
            "name": name,
            "scope": _attr_scope(raw, path),
            "attrType": _read_object(raw, path, "attrType", _normalize_attr_type),
        }
    if kind == "default":
        return {
            "kind": "default",
            "name": name,
            "value": _read_object(raw, path, "value", _normalize_attr_value),
        }
    return {
        "kind": "assignment",
        "name": name,
        "target": _read_object(raw, path, "target", _normalize_attr_target),
        "value": _read_object(raw, path, "value", _normalize_attr_value),
    }


def normalize_dbc(raw: ReplyFields) -> DBCDefinition:
    """Read the ``dbc`` object of a reply into a ``DBCDefinition``.

    A rational arrives as an integer or as the kernel's ``{numerator,
    denominator}`` object and is read as a ``Fraction``, the core's exact value.
    Every key the kernel writes is required: a reply without one is refused
    rather than filled in, each refusal naming its place from ``dbc``.
    """
    return {
        "version": _string(raw, _DBC, "version"),
        "messages": _normalize_messages(raw, _DBC),
        "signalGroups": _normalize_list(raw, _DBC, "signalGroups", _normalize_signal_group),
        "environmentVars": _normalize_list(
            raw, _DBC, "environmentVars", _normalize_environment_var
        ),
        "valueTables": _normalize_list(raw, _DBC, "valueTables", _normalize_value_table),
        "nodes": _normalize_list(raw, _DBC, "nodes", _normalize_node),
        "comments": _normalize_list(raw, _DBC, "comments", _normalize_comment),
        "attributes": _normalize_list(raw, _DBC, "attributes", _normalize_attribute),
        "unresolvedValueDescs": _normalize_list(
            raw, _DBC, "unresolvedValueDescs", _normalize_raw_value_desc
        ),
    }


# ----------------------------------------------------------------------------
# Reading one place: each reader narrows the value at ``key`` of the object at
# ``path`` and refuses any other in the one form, naming the place.
# ----------------------------------------------------------------------------


def _string(raw: ReplyFields, path: ReplyPath, key: LiteralString) -> str:
    """Read the string ``key`` holds in the object at ``path``."""
    if key in raw and isinstance(value := raw[key], str):
        return value
    raise reply_refusal(at(path, key), STRING, came(raw, key))


def _whole(raw: ReplyFields, path: ReplyPath, key: LiteralString) -> int:
    """Read the whole number ``key`` holds in the object at ``path``, written as digits."""
    if key in raw and is_pure_int(value := raw[key]):
        return value
    raise reply_refusal(at(path, key), NUMBER, came(raw, key))


def _boolean(raw: ReplyFields, path: ReplyPath, key: LiteralString) -> bool:
    """Read the boolean ``key`` holds in the object at ``path``."""
    if key in raw and isinstance(value := raw[key], bool):
        return value
    raise reply_refusal(at(path, key), BOOLEAN, came(raw, key))


def _rational(raw: ReplyFields, path: ReplyPath, key: LiteralString) -> Fraction:
    """Read the rational ``key`` holds in the object at ``path``, one place whatever its form."""
    if key not in raw:
        raise reply_refusal(at(path, key), A_RATIONAL, came(raw, key))
    return read_rational(raw[key], at(path, key))


def _array(raw: ReplyFields, path: ReplyPath, key: LiteralString) -> list[JSONValue]:
    """Read the array ``key`` holds in the object at ``path``."""
    if key in raw and isinstance(value := raw[key], list):
        return value
    raise reply_refusal(at(path, key), ARRAY, came(raw, key))


def _strings(raw: ReplyFields, path: ReplyPath, key: LiteralString) -> list[str]:
    """Read the array ``key`` holds in the object at ``path``, each entry a string."""
    place = at(path, key)
    return [_string_entry(entry, place) for entry in _array(raw, path, key)]


def _string_entry(entry: JSONValue, place: ReplyPath) -> str:
    """Read an entry of the array at ``place`` as a string."""
    if not isinstance(entry, str):
        raise reply_refusal(place, STRING, came_as(entry))
    return entry


def _read_object[T](
    raw: ReplyFields,
    path: ReplyPath,
    key: LiteralString,
    read: Callable[[ReplyFields, ReplyPath], T],
) -> T:
    """Read the object ``key`` holds in the object at ``path`` with ``read``."""
    if key in raw and is_str_dict(value := raw[key]):
        return read(value, at(path, key))
    raise reply_refusal(at(path, key), OBJECT, came(raw, key))


def _normalize_list[T](
    raw: ReplyFields,
    path: ReplyPath,
    key: LiteralString,
    read: Callable[[ReplyFields, ReplyPath], T],
) -> list[T]:
    """Read the array ``key`` holds in the object at ``path`` with ``read``, entry by entry."""
    place = at(path, key)
    entries: list[T] = []
    for entry in _array(raw, path, key):
        if not is_str_dict(entry):
            raise reply_refusal(place, OBJECT, came_as(entry))
        entries.append(read(entry, place))
    return entries
