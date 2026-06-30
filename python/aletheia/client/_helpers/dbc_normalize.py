# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Outbound (TypedDict → wire JSON) and inbound (Agda formatDBC → DBCDefinition) normalisation."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast, get_args

from aletheia.client._helpers.rational import decode_wire_rational, is_pure_int, reject_inexact
from aletheia.client._types import (
    DLCByteCount,
    ProtocolError,
    ValidationError,
    bytes_to_dlc,
    validate_can_id,
)
from aletheia.types import (
    AttrScope,
    DBCAttrAssign,
    DBCAttrDef,
    DBCAttrDefault,
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
    is_object_list,
    is_str_dict,
)

if TYPE_CHECKING:
    from collections.abc import Callable, Mapping

    from aletheia.types import JSONValue

# Fields in a DBCSignal that Agda serializes as JNumber (may be rational dict)
_NUMERIC_SIGNAL_FIELDS = ("factor", "offset", "minimum", "maximum")

# Signal bit-layout bounds the core guarantees (see Aletheia.DBC.SignalWF).
_MAX_START_BIT = 511
_MAX_BIT_LENGTH = 64
# Multiplex selector values are u32 (cross-binding parity with Go/C++/Rust).
_MAX_MULTIPLEX_VALUE = (1 << 32) - 1

# Fields in a DBCEnvironmentVar that carry ℚ on the Agda wire.
_NUMERIC_ENV_VAR_FIELDS = ("initial", "minimum", "maximum")


# Outgoing-DBC normalization: C++/Go always emit these list keys (their
# structs hold non-optional list fields), while Python's TypedDict uses
# ``NotRequired`` so callers may omit them.  Filling in `[]` defaults
# before serialization aligns Python's wire shape with C++/Go — every
# binding's FFI dispatcher sees the same JSON envelope.  Per
# `feedback_cross_binding_wire_symmetry`.
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

    The outbound twin of ``normalize_signal``'s inbound ``decode_wire_rational``:
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
    ``decode_wire_rational`` (via ``reject_inexact``, which rejects both a
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

    The float principle (the outbound twin of the inbound ``decode_wire_rational``):
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
def normalize_signal(raw_sig: Mapping[str, JSONValue]) -> DBCSignal:
    """Normalize a single Agda signal dict into a DBCSignal."""
    sig: dict[str, object] = {}
    sig.update(raw_sig)
    for field in _NUMERIC_SIGNAL_FIELDS:
        if field in sig:
            sig[field] = decode_wire_rational(sig[field])
    _validate_signal_bits(sig)
    _validate_signal_presence(sig)
    return cast("DBCSignal", sig)


def _validate_signal_bits(sig: Mapping[str, object]) -> None:
    """Reject an out-of-range startBit (0-511) or bit length (1-64)."""
    start_bit = sig.get("startBit")
    if not is_pure_int(start_bit) or not 0 <= start_bit <= _MAX_START_BIT:
        msg = f"Expected signal 'startBit' in 0-{_MAX_START_BIT}, got {start_bit!r}"
        raise ProtocolError(msg)
    length = sig.get("length")
    if not is_pure_int(length) or not 1 <= length <= _MAX_BIT_LENGTH:
        msg = f"Expected signal 'length' in 1-{_MAX_BIT_LENGTH}, got {length!r}"
        raise ProtocolError(msg)


def _validate_signal_presence(sig: Mapping[str, object]) -> None:
    """Validate the explicit ``presence`` discriminator the core emits.

    Mirrors the Rust binding: ``presence`` is required and must be ``"always"``
    or ``"multiplexed"``; a multiplexed signal additionally requires a non-empty
    ``multiplexor`` and a non-empty ``multiplex_values`` list of non-negative
    integers.
    """
    presence = sig.get("presence")
    if presence == "always":
        return
    if presence == "multiplexed":
        multiplexor = sig.get("multiplexor")
        if not isinstance(multiplexor, str) or not multiplexor:
            msg = "Multiplexed signal requires a non-empty 'multiplexor'"
            raise ProtocolError(msg)
        values = sig.get("multiplex_values")
        if not isinstance(values, list) or not values:
            msg = "Multiplexed signal requires a non-empty 'multiplex_values' array"
            raise ProtocolError(msg)
        for entry in cast("list[object]", values):
            if not is_pure_int(entry) or not 0 <= entry <= _MAX_MULTIPLEX_VALUE:
                msg = (
                    f"Expected 'multiplex_values' entry in 0-{_MAX_MULTIPLEX_VALUE}, got {entry!r}"
                )
                raise ProtocolError(msg)
        return
    msg = f"Expected signal 'presence' to be 'always' or 'multiplexed', got {presence!r}"
    raise ProtocolError(msg)


def _normalize_signal_group(raw: Mapping[str, JSONValue]) -> DBCSignalGroup:
    """Normalize one ``signalGroups`` entry from Agda formatDBC output."""
    name = raw.get("name")
    if not isinstance(name, str):
        msg = "Expected signal group 'name' to be str"
        raise ProtocolError(msg)
    raw_signals = raw.get("signals")
    if not is_object_list(raw_signals):
        msg = "Expected signal group 'signals' to be a list"
        raise ProtocolError(msg)
    signals: list[str] = []
    for s in raw_signals:
        if not isinstance(s, str):
            msg = "Expected signal group member to be str"
            raise ProtocolError(msg)
        signals.append(s)
    return {"name": name, "signals": signals}


def _normalize_var_type(raw: object) -> DBCVarType:
    """Narrow an Agda ``varType`` (ℕ 0/1/2) to the ``DBCVarType`` Literal."""
    if not is_pure_int(raw) or raw not in (0, 1, 2):
        msg = f"Expected environment var 'varType' to be 0, 1, or 2, got {raw!r}"
        raise ProtocolError(msg)
    return raw


def _normalize_environment_var(raw: Mapping[str, JSONValue]) -> DBCEnvironmentVar:
    """Normalize one ``environmentVars`` entry from Agda formatDBC output."""
    name = raw.get("name")
    if not isinstance(name, str):
        msg = "Expected environment var 'name' to be str"
        raise ProtocolError(msg)
    ev: dict[str, object] = {
        "name": name,
        "varType": _normalize_var_type(raw.get("varType")),
    }
    for field in _NUMERIC_ENV_VAR_FIELDS:
        if field not in raw:
            msg = f"Expected environment var field {field!r}"
            raise ProtocolError(msg)
        ev[field] = decode_wire_rational(raw[field])
    return cast("DBCEnvironmentVar", ev)


def _normalize_value_entry(raw: Mapping[str, JSONValue]) -> DBCValueEntry:
    """Normalize one ``entries`` item from a ``valueTables`` entry."""
    value_raw = raw.get("value")
    if not is_pure_int(value_raw) or value_raw < 0:
        msg = f"Expected value table entry 'value' to be non-negative int, got {value_raw!r}"
        raise ProtocolError(msg)
    desc = raw.get("description")
    if not isinstance(desc, str):
        msg = "Expected value table entry 'description' to be str"
        raise ProtocolError(msg)
    return {"value": value_raw, "description": desc}


def _normalize_value_table(raw: Mapping[str, JSONValue]) -> DBCValueTable:
    """Normalize one ``valueTables`` entry from Agda formatDBC output."""
    name = raw.get("name")
    if not isinstance(name, str):
        msg = "Expected value table 'name' to be str"
        raise ProtocolError(msg)
    raw_entries = raw.get("entries")
    if not is_object_list(raw_entries):
        msg = "Expected value table 'entries' to be a list"
        raise ProtocolError(msg)
    entries: list[DBCValueEntry] = []
    for e in raw_entries:
        if not is_str_dict(e):
            msg = "Expected value table entry to be a dict"
            raise ProtocolError(msg)
        entries.append(_normalize_value_entry(e))
    return {"name": name, "entries": entries}


def _normalize_raw_value_desc(raw: Mapping[str, JSONValue]) -> DBCRawValueDesc:
    """Normalize one ``unresolvedValueDescs`` entry from Agda formatDBC output.

    Track E.8 (Plan B): wire shape is ``{id, [extended], signalName, entries}``,
    paralleling ``DBCMessage`` for the CAN-ID half.
    """
    raw_entries = raw.get("entries")
    if not is_object_list(raw_entries):
        msg = "Expected unresolvedValueDescs 'entries' to be a list"
        raise ProtocolError(msg)
    entries: list[DBCValueEntry] = []
    for e in raw_entries:
        if not is_str_dict(e):
            msg = "Expected unresolvedValueDescs entry to be a dict"
            raise ProtocolError(msg)
        entries.append(_normalize_value_entry(e))
    out: dict[str, object] = {
        "id": _require_int_field(raw, "id", "unresolvedValueDesc"),
        "signalName": _require_str_field(raw, "signalName", "unresolvedValueDesc"),
        "entries": entries,
    }
    if _optional_extended(raw):
        out["extended"] = True
    return cast("DBCRawValueDesc", out)


# ----------------------------------------------------------------------------
# Tier 2 metadata normalisation (nodes / comments / attributes)
# ----------------------------------------------------------------------------


def _require_str_field(raw: Mapping[str, JSONValue], field: str, context: str) -> str:
    v = raw.get(field)
    if not isinstance(v, str):
        msg = f"Expected {context} {field!r} to be str, got {type(v).__name__}"
        raise ProtocolError(msg)
    return v


def _require_int_field(raw: Mapping[str, JSONValue], field: str, context: str) -> int:
    v = raw.get(field)
    if not is_pure_int(v):
        msg = f"Expected {context} {field!r} to be int, got {type(v).__name__}"
        raise ProtocolError(msg)
    return v


def _optional_extended(raw: Mapping[str, JSONValue]) -> bool:
    """Accept an optional ``extended`` flag (default ``False``).

    Agda emits it only for 29-bit IDs, but the Python side always passes it
    through to preserve round-trip wire shape.
    """
    v = raw.get("extended")
    if v is None:
        return False
    if not isinstance(v, bool):
        msg = f"Expected 'extended' to be bool, got {type(v).__name__}"
        raise ProtocolError(msg)
    return v


def _normalize_node(raw: Mapping[str, JSONValue]) -> DBCNode:
    return {"name": _require_str_field(raw, "name", "node")}


def _normalize_comment_target(raw: Mapping[str, JSONValue]) -> DBCCommentTarget:
    kind = _require_str_field(raw, "kind", "comment target")
    if kind == "network":
        return {"kind": "network"}
    if kind == "node":
        return {"kind": "node", "node": _require_str_field(raw, "node", "comment target")}
    if kind == "message":
        out: dict[str, object] = {
            "kind": "message",
            "id": _require_int_field(raw, "id", "comment target"),
        }
        if _optional_extended(raw):
            out["extended"] = True
        return cast("DBCCommentTarget", out)
    if kind == "signal":
        out2: dict[str, object] = {
            "kind": "signal",
            "id": _require_int_field(raw, "id", "comment target"),
            "signal": _require_str_field(raw, "signal", "comment target"),
        }
        if _optional_extended(raw):
            out2["extended"] = True
        return cast("DBCCommentTarget", out2)
    if kind == "envVar":
        return {"kind": "envVar", "envVar": _require_str_field(raw, "envVar", "comment target")}
    msg = f"Unknown comment target kind {kind!r}"
    raise ProtocolError(msg)


def _normalize_comment(raw: Mapping[str, JSONValue]) -> DBCComment:
    target_raw = raw.get("target")
    if not is_str_dict(target_raw):
        msg = "Expected comment 'target' to be a dict"
        raise ProtocolError(msg)
    return {
        "target": _normalize_comment_target(target_raw),
        "text": _require_str_field(raw, "text", "comment"),
    }


# Membership set of the attr-scope wire names, derived from the ``AttrScope``
# Literal so the names live in exactly one place.  ``test_dbc_metadata_tier2``
# pins the round-trip order against the same ``get_args(AttrScope)`` sequence.
_ATTR_SCOPE_WIRE: frozenset[str] = frozenset(get_args(AttrScope))


def _normalize_attr_scope(value: object) -> AttrScope:
    if isinstance(value, str) and value in _ATTR_SCOPE_WIRE:
        return cast("AttrScope", value)
    msg = f"Unknown attribute scope {value!r}"
    raise ProtocolError(msg)


def _normalize_attr_type(raw: Mapping[str, JSONValue]) -> DBCAttrType:
    kind = _require_str_field(raw, "kind", "attribute type")
    if kind == "int":
        return {
            "kind": "int",
            "min": _require_int_field(raw, "min", "attribute type int"),
            "max": _require_int_field(raw, "max", "attribute type int"),
        }
    if kind == "float":
        if "min" not in raw or "max" not in raw:
            msg = "Expected attribute type float 'min' and 'max'"
            raise ProtocolError(msg)
        return {
            "kind": "float",
            "min": decode_wire_rational(raw["min"]),
            "max": decode_wire_rational(raw["max"]),
        }
    if kind == "string":
        return {"kind": "string"}
    if kind == "enum":
        raw_values = raw.get("values")
        if not is_object_list(raw_values):
            msg = "Expected attribute type enum 'values' to be a list"
            raise ProtocolError(msg)
        labels: list[str] = []
        for v in raw_values:
            if not isinstance(v, str):
                msg = "Expected attribute type enum 'values' entry to be str"
                raise ProtocolError(msg)
            labels.append(v)
        return {"kind": "enum", "values": labels}
    if kind == "hex":
        return {
            "kind": "hex",
            "min": _require_int_field(raw, "min", "attribute type hex"),
            "max": _require_int_field(raw, "max", "attribute type hex"),
        }
    msg = f"Unknown attribute type kind {kind!r}"
    raise ProtocolError(msg)


def _normalize_attr_value(raw: Mapping[str, JSONValue]) -> DBCAttrValue:
    kind = _require_str_field(raw, "kind", "attribute value")
    if kind == "int":
        return {"kind": "int", "value": _require_int_field(raw, "value", "attribute value int")}
    if kind == "float":
        if "value" not in raw:
            msg = "Expected attribute value float 'value'"
            raise ProtocolError(msg)
        return {"kind": "float", "value": decode_wire_rational(raw["value"])}
    if kind == "string":
        value = _require_str_field(raw, "value", "attribute value string")
        return {"kind": "string", "value": value}
    if kind == "enum":
        return {"kind": "enum", "value": _require_int_field(raw, "value", "attribute value enum")}
    if kind == "hex":
        return {"kind": "hex", "value": _require_int_field(raw, "value", "attribute value hex")}
    msg = f"Unknown attribute value kind {kind!r}"
    raise ProtocolError(msg)


def _with_optional_extended(
    raw: Mapping[str, JSONValue],
    base: dict[str, object],
) -> dict[str, object]:
    if _optional_extended(raw):
        base["extended"] = True
    return base


def _normalize_attr_target_msg_id(
    raw: Mapping[str, JSONValue],
    kind: str,
) -> dict[str, object]:
    return _with_optional_extended(
        raw,
        {
            "kind": kind,
            "id": _require_int_field(raw, "id", "attribute target"),
        },
    )


_ATTR_TARGET_SIMPLE_KINDS = frozenset({"network", "node", "envVar"})
_ATTR_TARGET_MSG_KINDS = frozenset({"message", "signal", "nodeMsg", "nodeSig"})


def _normalize_attr_target_simple(
    kind: str,
    raw: Mapping[str, JSONValue],
) -> dict[str, object]:
    ctx = "attribute target"
    if kind == "network":
        return {"kind": "network"}
    if kind == "node":
        return {"kind": "node", "node": _require_str_field(raw, "node", ctx)}
    return {"kind": "envVar", "envVar": _require_str_field(raw, "envVar", ctx)}


def _normalize_attr_target_msg(
    kind: str,
    raw: Mapping[str, JSONValue],
) -> dict[str, object]:
    ctx = "attribute target"
    base = _normalize_attr_target_msg_id(raw, kind)
    if kind in ("nodeMsg", "nodeSig"):
        base["node"] = _require_str_field(raw, "node", ctx)
    if kind in ("signal", "nodeSig"):
        base["signal"] = _require_str_field(raw, "signal", ctx)
    return base


def _normalize_attr_target(raw: Mapping[str, JSONValue]) -> DBCAttrTarget:
    kind = _require_str_field(raw, "kind", "attribute target")
    if kind in _ATTR_TARGET_SIMPLE_KINDS:
        return cast("DBCAttrTarget", _normalize_attr_target_simple(kind, raw))
    if kind in _ATTR_TARGET_MSG_KINDS:
        return cast("DBCAttrTarget", _normalize_attr_target_msg(kind, raw))
    msg = f"Unknown attribute target kind {kind!r}"
    raise ProtocolError(msg)


def _normalize_attribute(raw: Mapping[str, JSONValue]) -> DBCAttribute:
    kind = _require_str_field(raw, "kind", "attribute")
    name = _require_str_field(raw, "name", "attribute")
    if kind == "definition":
        scope = _normalize_attr_scope(raw.get("scope"))
        attr_type_raw = raw.get("attrType")
        if not is_str_dict(attr_type_raw):
            msg = "Expected attribute 'attrType' to be a dict"
            raise ProtocolError(msg)
        result_def: DBCAttrDef = {
            "kind": "definition",
            "name": name,
            "scope": scope,
            "attrType": _normalize_attr_type(attr_type_raw),
        }
        return result_def
    if kind == "default":
        value_raw = raw.get("value")
        if not is_str_dict(value_raw):
            msg = "Expected attribute default 'value' to be a dict"
            raise ProtocolError(msg)
        result_default: DBCAttrDefault = {
            "kind": "default",
            "name": name,
            "value": _normalize_attr_value(value_raw),
        }
        return result_default
    if kind == "assignment":
        target_raw = raw.get("target")
        if not is_str_dict(target_raw):
            msg = "Expected attribute assignment 'target' to be a dict"
            raise ProtocolError(msg)
        value_raw = raw.get("value")
        if not is_str_dict(value_raw):
            msg = "Expected attribute assignment 'value' to be a dict"
            raise ProtocolError(msg)
        result_assign: DBCAttrAssign = {
            "kind": "assignment",
            "name": name,
            "target": _normalize_attr_target(target_raw),
            "value": _normalize_attr_value(value_raw),
        }
        return result_assign
    msg = f"Unknown attribute kind {kind!r}"
    raise ProtocolError(msg)


def _validate_message_meta(message: Mapping[str, object]) -> None:
    """Reject an out-of-range CAN id (per ``extended``) or invalid DLC byte count.

    Reuses the binding's canonical ``validate_can_id`` / ``bytes_to_dlc`` bounds
    (the SSOT), re-raising their ``ValidationError`` as a ``ProtocolError`` to
    keep the decode path's error type uniform.
    """
    can_id = message.get("id")
    if not is_pure_int(can_id):
        msg = f"Expected message 'id' to be an int, got {can_id!r}"
        raise ProtocolError(msg)
    extended = message.get("extended", False)
    if not isinstance(extended, bool):
        msg = f"Expected message 'extended' to be a bool, got {extended!r}"
        raise ProtocolError(msg)
    dlc = message.get("dlc")
    if not is_pure_int(dlc):
        msg = f"Expected message 'dlc' to be an int, got {dlc!r}"
        raise ProtocolError(msg)
    try:
        validate_can_id(can_id, extended=extended)
        bytes_to_dlc(DLCByteCount(dlc))
    except ValidationError as e:
        raise ProtocolError(str(e)) from e


def normalize_dbc(raw: Mapping[str, JSONValue]) -> DBCDefinition:
    """Normalize Agda's formatDBC JSON into a proper DBCDefinition.

    Agda's ``formatRational`` encodes non-integer rationals as
    ``{"numerator": n, "denominator": d}`` dicts. This method
    converts those to ``Fraction`` so the result matches the
    ``DBCDefinition`` TypedDict and preserves the core's exact
    rational precision end-to-end.

    The three metadata arrays (signalGroups / environmentVars / valueTables)
    are treated as optional on input — Agda formatDBC always emits them,
    but the caller may omit them in hand-built fixtures.
    """
    raw_messages = raw.get("messages")
    if not is_object_list(raw_messages):
        msg = "Expected 'messages' to be a list"
        raise ProtocolError(msg)
    messages: list[DBCMessage] = []
    for m in raw_messages:
        if not is_str_dict(m):
            msg = "Expected each message to be a dict"
            raise ProtocolError(msg)
        raw_signals = m.get("signals")
        if not is_object_list(raw_signals):
            msg = "Expected 'signals' to be a list"
            raise ProtocolError(msg)
        signals: list[DBCSignal] = []
        for s in raw_signals:
            if not is_str_dict(s):
                msg = "Expected each signal to be a dict"
                raise ProtocolError(msg)
            signals.append(normalize_signal(s))
        msg_dict: dict[str, object] = dict(m)
        msg_dict["signals"] = signals
        _validate_message_meta(msg_dict)
        messages.append(cast("DBCMessage", msg_dict))
    result: DBCDefinition = {
        "version": str(raw.get("version", "")),
        "messages": messages,
        "signalGroups": _normalize_optional_list(
            raw,
            "signalGroups",
            _normalize_signal_group,
        ),
        "environmentVars": _normalize_optional_list(
            raw,
            "environmentVars",
            _normalize_environment_var,
        ),
        "valueTables": _normalize_optional_list(
            raw,
            "valueTables",
            _normalize_value_table,
        ),
        "nodes": _normalize_optional_list(raw, "nodes", _normalize_node),
        "comments": _normalize_optional_list(raw, "comments", _normalize_comment),
        "attributes": _normalize_optional_list(raw, "attributes", _normalize_attribute),
        "unresolvedValueDescs": _normalize_optional_list(
            raw,
            "unresolvedValueDescs",
            _normalize_raw_value_desc,
        ),
    }
    return result


def _normalize_optional_list[T](
    raw: Mapping[str, JSONValue],
    key: str,
    item_parser: Callable[[Mapping[str, JSONValue]], T],
) -> list[T]:
    """Normalize a NotRequired metadata array: treat missing as empty."""
    if key not in raw:
        return []
    items = raw.get(key)
    if not is_object_list(items):
        msg = f"Expected {key!r} to be a list"
        raise ProtocolError(msg)
    parsed: list[T] = []
    for item in items:
        if not is_str_dict(item):
            msg = f"Expected each {key!r} entry to be a dict"
            raise ProtocolError(msg)
        parsed.append(item_parser(item))
    return parsed
