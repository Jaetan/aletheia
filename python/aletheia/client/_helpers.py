"""Pure helper functions for response parsing and type conversion."""

import json
import math
from collections.abc import Callable, Sequence
from fractions import Fraction
from typing import cast, override

from ..protocols import (
    AttrScope,
    DBCAttrDef,
    DBCAttrDefault,
    DBCAttrAssign,
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
    RationalNumber,
    is_str_dict,
    is_object_list,
)
from ._types import ProtocolError

# Fields in a DBCSignal that Agda serializes as JNumber (may be rational dict)
_NUMERIC_SIGNAL_FIELDS = ("factor", "offset", "minimum", "maximum")

# Fields in a DBCEnvironmentVar that carry ℚ on the Agda wire.
_NUMERIC_ENV_VAR_FIELDS = ("initial", "minimum", "maximum")


class FractionJSONEncoder(json.JSONEncoder):
    """JSONEncoder that serializes Fraction in Agda's canonical rational form.

    Mirrors ``Aletheia.Format.Rational.formatRational``: emit a bare integer
    when the denominator is 1, otherwise the ``{"numerator": n,
    "denominator": d}`` dict. Agda's ``parseRational`` accepts integer
    literals, rational dicts, and decimal floats, so this preserves exact
    precision on any DBCDefinition round-trip path while staying
    byte-identical to Go's ``serializeRational`` and C++'s
    ``serialize_rational`` — the cross-binding canonical form B.3.j gates on.
    """

    @override
    def default(self, o: object) -> object:
        if isinstance(o, Fraction):
            if o.denominator == 1:
                return o.numerator
            return {"numerator": o.numerator, "denominator": o.denominator}
        return super().default(o)


def dump_json(value: object, *, indent: int | None = None) -> str:
    """Serialize *value* to JSON, handling Fraction via FractionJSONEncoder."""
    return json.dumps(value, cls=FractionJSONEncoder, indent=indent)


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


# Shared bounds and scaling factors for the binary FFI rational encoding.
# int64 bounds match the Haskell ``Int64`` numerator/denominator that the
# Agda core consumes; the decimal precision denominator mirrors the 10^9
# scaling that Agda's ``formatRational`` emits on the JSON path so the two
# wire formats stay bit-identical on round-trip.
_INT64_MAX = (1 << 63) - 1
_INT64_MIN = -(1 << 63)
_DECIMAL_PRECISION_DEN = 1_000_000_000


def float_to_rational(value: float) -> tuple[int, int]:
    """Convert a float to (numerator, denominator) for binary FFI.

    Uses 10^9 scaling to match JSON decimal precision.
    The Haskell side normalizes to coprime form via GCD.

    Raises:
        ValueError: If *value* is NaN, infinite, or too large for int64.
    """
    if math.isnan(value) or math.isinf(value):
        raise ValueError(f"Cannot convert {value!r} to rational")
    numerator = round(value * _DECIMAL_PRECISION_DEN)
    # Guard against values that would overflow int64 in the binary FFI.
    # Use the full int64 range, not the 53-bit float mantissa bound — the
    # denominator is a compile-time constant ≤ int64 so any numerator that
    # fits int64 is safe to pack as ``<q`` little-endian.
    if not _INT64_MIN <= numerator <= _INT64_MAX:
        raise ValueError(
            f"signal value {value!r} too large for rational representation"
        )
    return (numerator, _DECIMAL_PRECISION_DEN)


def fraction_to_rational(value: Fraction) -> tuple[int, int]:
    """Convert a Fraction to (numerator, denominator) for binary FFI, lossless.

    Unlike float_to_rational this preserves exact precision — the Agda core
    works in ℚ and the wire format carries int64 numerator/denominator pairs,
    so Fractions flow through without the 10^9 quantization step.

    Raises:
        ValueError: If either component overflows int64.
    """
    n, d = value.numerator, value.denominator
    if not _INT64_MIN <= n <= _INT64_MAX or not _INT64_MIN <= d <= _INT64_MAX:
        raise ValueError(
            f"Fraction {value!r} components exceed int64 range"
        )
    return (n, d)


def coerce_to_rational(value: float | Fraction) -> tuple[int, int]:
    """Convert a numeric signal input to (numerator, denominator).

    Uses Fraction's exact representation when the caller already has one;
    falls back to float_to_rational's 10^9 scaling for float inputs.
    """
    if isinstance(value, Fraction):
        return fraction_to_rational(value)
    return float_to_rational(value)


def to_signal_fraction(value: float | int | Fraction) -> Fraction:
    """Convert a decimal-intent numeric input to a Fraction for DBCSignal fields.

    Floats are bounded via ``limit_denominator(1_000_000_000)`` so that
    decimal inputs like ``0.1`` become ``1/10`` exactly rather than the
    IEEE-754 approximation's monstrous denominator.  Int and existing
    Fraction inputs flow through unchanged.
    """
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int) and not isinstance(value, bool):
        return Fraction(value)
    return Fraction(value).limit_denominator(_DECIMAL_PRECISION_DEN)


def extract_rational_from_dict(
    d: dict[str, object], context: str,
) -> tuple[int, int]:
    """Extract (numerator, denominator) from a rational dict.

    Raises ProtocolError if the dict is malformed or denominator is zero.
    """
    numerator = d.get("numerator")
    denominator = d.get("denominator")
    if not isinstance(numerator, int):
        raise ProtocolError(f"Expected {context}.numerator to be int")
    if not isinstance(denominator, int):
        raise ProtocolError(f"Expected {context}.denominator to be int")
    if denominator == 0:
        raise ProtocolError(f"Expected {context}.denominator to be nonzero")
    return numerator, denominator


def validate_rational(field_name: str, raw_value: object) -> RationalNumber:
    """Validate and extract RationalNumber from response field."""
    if isinstance(raw_value, int):
        return {"numerator": raw_value, "denominator": 1}
    if not is_str_dict(raw_value):
        raise ProtocolError(
            f"Expected {field_name} to be int or dict, got {type(raw_value).__name__}"
        )
    n, d = extract_rational_from_dict(raw_value, field_name)
    return {"numerator": n, "denominator": d}


def parse_rational(value_raw: object) -> Fraction:
    """Parse a value that may be a number, rational dict, or rational string.

    Returns a Fraction to preserve the Agda core's exact rational precision
    end-to-end — JSON rational dicts {"numerator": n, "denominator": d}
    become Fraction(n, d) with no float quantization.

    For legacy float inputs (rare — Agda's formatRational emits integers as
    ints and non-integers as rational dicts) we still go through Fraction,
    using its float-from-string heuristic to avoid binary float artifacts.
    """
    if isinstance(value_raw, bool):
        # bool is a subclass of int; reject explicitly to avoid True → Fraction(1)
        raise ProtocolError(
            "Expected signal value to be number, rational dict, "
            + "or rational string, got bool"
        )
    if isinstance(value_raw, int):
        return Fraction(value_raw)
    if isinstance(value_raw, float):
        if math.isnan(value_raw) or math.isinf(value_raw):
            raise ProtocolError(f"Cannot convert {value_raw!r} to rational")
        return Fraction(value_raw).limit_denominator(_DECIMAL_PRECISION_DEN)
    if is_str_dict(value_raw):
        n, d = extract_rational_from_dict(value_raw, "rational")
        return Fraction(n, d)
    if isinstance(value_raw, str):
        if "/" in value_raw:
            parts = value_raw.split("/")
            if len(parts) == 2:
                try:
                    numerator_s = int(parts[0])
                    denominator_s = int(parts[1])
                except ValueError:
                    pass
                else:
                    if denominator_s == 0:
                        raise ProtocolError(
                            f"Division by zero in rational string: {value_raw!r}"
                        )
                    return Fraction(numerator_s, denominator_s)
        try:
            return Fraction(value_raw)
        except (ValueError, ZeroDivisionError):
            pass
    raise ProtocolError(
        "Expected signal value to be number, rational dict, "
        + f"or rational string, got {type(value_raw).__name__}"
    )


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
    if isinstance(raw, bool) or not isinstance(raw, int) or raw not in (0, 1, 2):
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
    if isinstance(value_raw, bool) or not isinstance(value_raw, int) or value_raw < 0:
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
    if isinstance(v, bool) or not isinstance(v, int):
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
    }
    result["signalGroups"] = _normalize_optional_list(
        raw, "signalGroups", _normalize_signal_group
    )
    result["environmentVars"] = _normalize_optional_list(
        raw, "environmentVars", _normalize_environment_var
    )
    result["valueTables"] = _normalize_optional_list(
        raw, "valueTables", _normalize_value_table
    )
    result["nodes"] = _normalize_optional_list(raw, "nodes", _normalize_node)
    result["comments"] = _normalize_optional_list(raw, "comments", _normalize_comment)
    result["attributes"] = _normalize_optional_list(raw, "attributes", _normalize_attribute)
    result["unresolvedValueDescs"] = _normalize_optional_list(
        raw, "unresolvedValueDescs", _normalize_raw_value_desc
    )
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


def parse_values_list(values_data: Sequence[object]) -> dict[str, Fraction]:
    """Parse signal values list from response."""
    values: dict[str, Fraction] = {}
    for item in values_data:
        if not is_str_dict(item):
            raise ProtocolError(f"Expected signal value to be dict, got {type(item)}")
        name_raw = item.get("name")
        if not isinstance(name_raw, str):
            raise ProtocolError(f"Expected signal name to be str, got {type(name_raw)}")
        value_raw = item.get("value")
        values[name_raw] = parse_rational(value_raw)
    return values


def parse_errors_list(errors_data: Sequence[object]) -> dict[str, str]:
    """Parse signal errors list from response."""
    errors: dict[str, str] = {}
    for item in errors_data:
        if not is_str_dict(item):
            raise ProtocolError(f"Expected error item to be dict, got {type(item)}")
        name_raw = item.get("name")
        if not isinstance(name_raw, str):
            raise ProtocolError(f"Expected error signal name to be str, got {type(name_raw)}")
        error_raw = item.get("error")
        if not isinstance(error_raw, str):
            raise ProtocolError(f"Expected error message to be str, got {type(error_raw)}")
        errors[name_raw] = error_raw
    return errors


def parse_absent_list(absent_data: Sequence[object]) -> list[str]:
    """Parse absent signals list from response."""
    absent: list[str] = []
    for item in absent_data:
        if not isinstance(item, str):
            raise ProtocolError(f"Expected absent signal name to be str, got {type(item)}")
        absent.append(item)
    return absent
