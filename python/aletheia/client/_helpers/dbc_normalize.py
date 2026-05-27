"""Outbound (Python TypedDict → wire JSON) and inbound (Agda formatDBC JSON
→ DBCDefinition) DBC normalisation."""

from collections.abc import Callable
from typing import cast

from aletheia.protocols import (
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
from aletheia._loader_utils import is_pure_int
from aletheia.client._types import ProtocolError
from aletheia.client._helpers.rational import parse_rational

# Fields in a DBCSignal that Agda serializes as JNumber (may be rational dict)
_NUMERIC_SIGNAL_FIELDS = ("factor", "offset", "minimum", "maximum")

# Fields in a DBCEnvironmentVar that carry ℚ on the Agda wire.
_NUMERIC_ENV_VAR_FIELDS = ("initial", "minimum", "maximum")


# Outgoing-DBC normalization: C++/Go always emit these list keys (their
# structs hold non-optional list fields), while Python's TypedDict uses
# ``NotRequired`` so callers may omit them.  Filling in `[]` defaults
# before serialization aligns Python's wire shape with C++/Go — every
# binding's FFI dispatcher sees the same JSON envelope.  Per
# `feedback_cross_binding_wire_symmetry`.
_DBC_TIER2_LIST_KEYS = (
    "signalGroups", "environmentVars", "valueTables",
    "nodes", "comments", "attributes", "unresolvedValueDescs",
)


def _normalize_signal_for_wire(sig: dict[str, object]) -> dict[str, object]:
    """Ensure NotRequired signal list fields are present in outgoing JSON."""
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


def normalize_dbc_for_wire(dbc: DBCDefinition) -> DBCDefinition:
    """Pad an outgoing ``DBCDefinition`` with empty defaults for absent list fields.

    C++/Go always emit the optional Tier-2 list keys (``nodes``, ``comments``,
    …) and the per-message ``senders`` / per-signal ``receivers`` /
    ``valueDescriptions`` because their language-level structs hold
    non-optional list fields.  Python's TypedDict ``NotRequired`` lets
    callers omit them.  This helper aligns Python's outgoing wire shape
    with C++/Go so the JSON envelope reaching the FFI dispatcher is
    identical regardless of which binding constructed the request.
    """
    messages = cast("list[dict[str, object]]", dbc.get("messages", []))
    result: dict[str, object] = {
        **dbc,
        "messages": [_normalize_message_for_wire(m) for m in messages],
    }
    for key in _DBC_TIER2_LIST_KEYS:
        if key not in result:
            result[key] = []
    return cast(DBCDefinition, result)


# DEFERRED — TRACKED (R19P2-CL16-4 — DEFER).
# Finding: `normalize_signal` is exposed publicly (no underscore prefix) but
#   only called by this module's internal helpers + tests.
# Why DEFER: Mechanical underscore-prefix + import update; same shape as
#   R19P2-CL16-3 (the wider boundary-naming sweep).
# Revisit when: Co-decided with R19P2-CL16-3.
def normalize_signal(raw_sig: dict[str, object]) -> DBCSignal:
    """Normalize a single Agda signal dict into a DBCSignal."""
    sig: dict[str, object] = dict(raw_sig)
    for field in _NUMERIC_SIGNAL_FIELDS:
        if field in sig:
            sig[field] = parse_rational(sig[field])
    return cast(DBCSignal, sig)


def _normalize_signal_group(raw: dict[str, object]) -> DBCSignalGroup:
    """Normalize one ``signalGroups`` entry from Agda formatDBC output."""
    name = raw.get("name")
    if not isinstance(name, str):
        raise ProtocolError("Expected signal group 'name' to be str")
    raw_signals = raw.get("signals")
    if not is_object_list(raw_signals):
        raise ProtocolError("Expected signal group 'signals' to be a list")
    signals: list[str] = []
    for s in raw_signals:
        if not isinstance(s, str):
            raise ProtocolError("Expected signal group member to be str")
        signals.append(s)
    return {"name": name, "signals": signals}


def _normalize_var_type(raw: object) -> DBCVarType:
    """Narrow an Agda ``varType`` (ℕ 0/1/2) to the ``DBCVarType`` Literal."""
    if not is_pure_int(raw) or raw not in (0, 1, 2):
        raise ProtocolError(
            f"Expected environment var 'varType' to be 0, 1, or 2, got {raw!r}"
        )
    return raw


def _normalize_environment_var(raw: dict[str, object]) -> DBCEnvironmentVar:
    """Normalize one ``environmentVars`` entry from Agda formatDBC output."""
    name = raw.get("name")
    if not isinstance(name, str):
        raise ProtocolError("Expected environment var 'name' to be str")
    ev: dict[str, object] = {
        "name": name,
        "varType": _normalize_var_type(raw.get("varType")),
    }
    for field in _NUMERIC_ENV_VAR_FIELDS:
        if field not in raw:
            raise ProtocolError(f"Expected environment var field {field!r}")
        ev[field] = parse_rational(raw[field])
    return cast(DBCEnvironmentVar, ev)


def _normalize_value_entry(raw: dict[str, object]) -> DBCValueEntry:
    """Normalize one ``entries`` item from a ``valueTables`` entry."""
    value_raw = raw.get("value")
    if not is_pure_int(value_raw) or value_raw < 0:
        raise ProtocolError(
            f"Expected value table entry 'value' to be non-negative int, got {value_raw!r}"
        )
    desc = raw.get("description")
    if not isinstance(desc, str):
        raise ProtocolError("Expected value table entry 'description' to be str")
    return {"value": value_raw, "description": desc}


def _normalize_value_table(raw: dict[str, object]) -> DBCValueTable:
    """Normalize one ``valueTables`` entry from Agda formatDBC output."""
    name = raw.get("name")
    if not isinstance(name, str):
        raise ProtocolError("Expected value table 'name' to be str")
    raw_entries = raw.get("entries")
    if not is_object_list(raw_entries):
        raise ProtocolError("Expected value table 'entries' to be a list")
    entries: list[DBCValueEntry] = []
    for e in raw_entries:
        if not is_str_dict(e):
            raise ProtocolError("Expected value table entry to be a dict")
        entries.append(_normalize_value_entry(e))
    return {"name": name, "entries": entries}


def _normalize_raw_value_desc(raw: dict[str, object]) -> "DBCRawValueDesc":
    """Normalize one ``unresolvedValueDescs`` entry from Agda formatDBC output.

    Track E.8 (Plan B): wire shape is ``{id, [extended], signalName, entries}``,
    paralleling ``DBCMessage`` for the CAN-ID half.
    """
    raw_entries = raw.get("entries")
    if not is_object_list(raw_entries):
        raise ProtocolError(
            "Expected unresolvedValueDescs 'entries' to be a list"
        )
    entries: list[DBCValueEntry] = []
    for e in raw_entries:
        if not is_str_dict(e):
            raise ProtocolError(
                "Expected unresolvedValueDescs entry to be a dict"
            )
        entries.append(_normalize_value_entry(e))
    out: dict[str, object] = {
        "id": _require_int_field(raw, "id", "unresolvedValueDesc"),
        "signalName": _require_str_field(
            raw, "signalName", "unresolvedValueDesc"
        ),
        "entries": entries,
    }
    if _optional_extended(raw):
        out["extended"] = True
    return cast("DBCRawValueDesc", out)


# ----------------------------------------------------------------------------
# Tier 2 metadata normalisation (nodes / comments / attributes)
# ----------------------------------------------------------------------------


def _require_str_field(raw: dict[str, object], field: str, context: str) -> str:
    v = raw.get(field)
    if not isinstance(v, str):
        raise ProtocolError(f"Expected {context} {field!r} to be str, got {type(v).__name__}")
    return v


def _require_int_field(raw: dict[str, object], field: str, context: str) -> int:
    v = raw.get(field)
    if not is_pure_int(v):
        raise ProtocolError(f"Expected {context} {field!r} to be int, got {type(v).__name__}")
    return v


def _optional_extended(raw: dict[str, object]) -> bool:
    """Accept an optional ``extended`` flag (default ``False``) — Agda emits
    it only for 29-bit IDs, but the Python side always passes it through to
    preserve round-trip wire shape."""
    v = raw.get("extended")
    if v is None:
        return False
    if not isinstance(v, bool):
        raise ProtocolError(f"Expected 'extended' to be bool, got {type(v).__name__}")
    return v


def _normalize_node(raw: dict[str, object]) -> DBCNode:
    return {"name": _require_str_field(raw, "name", "node")}


def _normalize_comment_target(raw: dict[str, object]) -> DBCCommentTarget:
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
        return cast(DBCCommentTarget, out)
    if kind == "signal":
        out2: dict[str, object] = {
            "kind": "signal",
            "id": _require_int_field(raw, "id", "comment target"),
            "signal": _require_str_field(raw, "signal", "comment target"),
        }
        if _optional_extended(raw):
            out2["extended"] = True
        return cast(DBCCommentTarget, out2)
    if kind == "envVar":
        return {"kind": "envVar", "envVar": _require_str_field(raw, "envVar", "comment target")}
    raise ProtocolError(f"Unknown comment target kind {kind!r}")


def _normalize_comment(raw: dict[str, object]) -> DBCComment:
    target_raw = raw.get("target")
    if not is_str_dict(target_raw):
        raise ProtocolError("Expected comment 'target' to be a dict")
    return {
        "target": _normalize_comment_target(target_raw),
        "text": _require_str_field(raw, "text", "comment"),
    }


_ATTR_SCOPE_WIRE: frozenset[str] = frozenset({
    "network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig",
})


def _normalize_attr_scope(value: object) -> AttrScope:
    if isinstance(value, str) and value in _ATTR_SCOPE_WIRE:
        return cast(AttrScope, value)
    raise ProtocolError(f"Unknown attribute scope {value!r}")


def _normalize_attr_type(raw: dict[str, object]) -> DBCAttrType:
    kind = _require_str_field(raw, "kind", "attribute type")
    if kind == "int":
        return {
            "kind": "int",
            "min": _require_int_field(raw, "min", "attribute type int"),
            "max": _require_int_field(raw, "max", "attribute type int"),
        }
    if kind == "float":
        if "min" not in raw or "max" not in raw:
            raise ProtocolError("Expected attribute type float 'min' and 'max'")
        return {
            "kind": "float",
            "min": parse_rational(raw["min"]),
            "max": parse_rational(raw["max"]),
        }
    if kind == "string":
        return {"kind": "string"}
    if kind == "enum":
        raw_values = raw.get("values")
        if not is_object_list(raw_values):
            raise ProtocolError("Expected attribute type enum 'values' to be a list")
        labels: list[str] = []
        for v in raw_values:
            if not isinstance(v, str):
                raise ProtocolError("Expected attribute type enum 'values' entry to be str")
            labels.append(v)
        return {"kind": "enum", "values": labels}
    if kind == "hex":
        return {
            "kind": "hex",
            "min": _require_int_field(raw, "min", "attribute type hex"),
            "max": _require_int_field(raw, "max", "attribute type hex"),
        }
    raise ProtocolError(f"Unknown attribute type kind {kind!r}")


def _normalize_attr_value(raw: dict[str, object]) -> DBCAttrValue:
    kind = _require_str_field(raw, "kind", "attribute value")
    if kind == "int":
        return {"kind": "int", "value": _require_int_field(raw, "value", "attribute value int")}
    if kind == "float":
        if "value" not in raw:
            raise ProtocolError("Expected attribute value float 'value'")
        return {"kind": "float", "value": parse_rational(raw["value"])}
    if kind == "string":
        value = _require_str_field(raw, "value", "attribute value string")
        return {"kind": "string", "value": value}
    if kind == "enum":
        return {"kind": "enum", "value": _require_int_field(raw, "value", "attribute value enum")}
    if kind == "hex":
        return {"kind": "hex", "value": _require_int_field(raw, "value", "attribute value hex")}
    raise ProtocolError(f"Unknown attribute value kind {kind!r}")


def _with_optional_extended(
    raw: dict[str, object], base: dict[str, object],
) -> dict[str, object]:
    if _optional_extended(raw):
        base["extended"] = True
    return base


def _normalize_attr_target_msg_id(
    raw: dict[str, object], kind: str,
) -> dict[str, object]:
    return _with_optional_extended(raw, {
        "kind": kind,
        "id": _require_int_field(raw, "id", "attribute target"),
    })


_ATTR_TARGET_SIMPLE_KINDS = frozenset({"network", "node", "envVar"})
_ATTR_TARGET_MSG_KINDS = frozenset({"message", "signal", "nodeMsg", "nodeSig"})


def _normalize_attr_target_simple(
    kind: str, raw: dict[str, object],
) -> dict[str, object]:
    ctx = "attribute target"
    if kind == "network":
        return {"kind": "network"}
    if kind == "node":
        return {"kind": "node", "node": _require_str_field(raw, "node", ctx)}
    return {"kind": "envVar", "envVar": _require_str_field(raw, "envVar", ctx)}


def _normalize_attr_target_msg(
    kind: str, raw: dict[str, object],
) -> dict[str, object]:
    ctx = "attribute target"
    base = _normalize_attr_target_msg_id(raw, kind)
    if kind in ("nodeMsg", "nodeSig"):
        base["node"] = _require_str_field(raw, "node", ctx)
    if kind in ("signal", "nodeSig"):
        base["signal"] = _require_str_field(raw, "signal", ctx)
    return base


def _normalize_attr_target(raw: dict[str, object]) -> DBCAttrTarget:
    kind = _require_str_field(raw, "kind", "attribute target")
    if kind in _ATTR_TARGET_SIMPLE_KINDS:
        return cast(DBCAttrTarget, _normalize_attr_target_simple(kind, raw))
    if kind in _ATTR_TARGET_MSG_KINDS:
        return cast(DBCAttrTarget, _normalize_attr_target_msg(kind, raw))
    raise ProtocolError(f"Unknown attribute target kind {kind!r}")


def _normalize_attribute(raw: dict[str, object]) -> DBCAttribute:
    kind = _require_str_field(raw, "kind", "attribute")
    name = _require_str_field(raw, "name", "attribute")
    if kind == "definition":
        scope = _normalize_attr_scope(raw.get("scope"))
        attr_type_raw = raw.get("attrType")
        if not is_str_dict(attr_type_raw):
            raise ProtocolError("Expected attribute 'attrType' to be a dict")
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
            raise ProtocolError("Expected attribute default 'value' to be a dict")
        result_default: DBCAttrDefault = {
            "kind": "default",
            "name": name,
            "value": _normalize_attr_value(value_raw),
        }
        return result_default
    if kind == "assignment":
        target_raw = raw.get("target")
        if not is_str_dict(target_raw):
            raise ProtocolError("Expected attribute assignment 'target' to be a dict")
        value_raw = raw.get("value")
        if not is_str_dict(value_raw):
            raise ProtocolError("Expected attribute assignment 'value' to be a dict")
        result_assign: DBCAttrAssign = {
            "kind": "assignment",
            "name": name,
            "target": _normalize_attr_target(target_raw),
            "value": _normalize_attr_value(value_raw),
        }
        return result_assign
    raise ProtocolError(f"Unknown attribute kind {kind!r}")


def normalize_dbc(raw: dict[str, object]) -> DBCDefinition:
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
        raise ProtocolError("Expected 'messages' to be a list")
    messages: list[DBCMessage] = []
    for m in raw_messages:
        if not is_str_dict(m):
            raise ProtocolError("Expected each message to be a dict")
        raw_signals = m.get("signals")
        if not is_object_list(raw_signals):
            raise ProtocolError("Expected 'signals' to be a list")
        signals: list[DBCSignal] = []
        for s in raw_signals:
            if not is_str_dict(s):
                raise ProtocolError("Expected each signal to be a dict")
            signals.append(normalize_signal(s))
        msg: dict[str, object] = dict(m)
        msg["signals"] = signals
        messages.append(cast(DBCMessage, msg))
    result: DBCDefinition = {
        "version": str(raw.get("version", "")),
        "messages": messages,
        "signalGroups": _normalize_optional_list(
            raw, "signalGroups", _normalize_signal_group,
        ),
        "environmentVars": _normalize_optional_list(
            raw, "environmentVars", _normalize_environment_var,
        ),
        "valueTables": _normalize_optional_list(
            raw, "valueTables", _normalize_value_table,
        ),
        "nodes": _normalize_optional_list(raw, "nodes", _normalize_node),
        "comments": _normalize_optional_list(raw, "comments", _normalize_comment),
        "attributes": _normalize_optional_list(raw, "attributes", _normalize_attribute),
        "unresolvedValueDescs": _normalize_optional_list(
            raw, "unresolvedValueDescs", _normalize_raw_value_desc,
        ),
    }
    return result


def _normalize_optional_list[T](
    raw: dict[str, object],
    key: str,
    item_parser: "Callable[[dict[str, object]], T]",
) -> list[T]:
    """Normalize a NotRequired metadata array: treat missing as empty."""
    if key not in raw:
        return []
    items = raw.get(key)
    if not is_object_list(items):
        raise ProtocolError(f"Expected {key!r} to be a list")
    parsed: list[T] = []
    for item in items:
        if not is_str_dict(item):
            raise ProtocolError(f"Expected each {key!r} entry to be a dict")
        parsed.append(item_parser(item))
    return parsed
