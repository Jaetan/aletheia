"""
Convert between .dbc files, JSON, and DBC text format.

- ``dbc_to_json``: Parse .dbc file to JSON (via cantools).
- ``dbc_to_text``: Convert JSON dict back to .dbc text.
- ``convert_dbc_file``: Parse .dbc to JSON string, optionally write to file.
"""

from fractions import Fraction
from pathlib import Path
from typing import cast

import cantools
import cantools.database.can
from cantools.database.can.attribute import Attribute as CantoolsAttribute
from cantools.database.can.attribute_definition import (
    AttributeDefinition as CantoolsAttrDefinition,
)
from cantools.database.can.database import Database as CantoolsDatabase
from cantools.database.can.environment_variable import (
    EnvironmentVariable as CantoolsEnvironmentVariable,
)
from cantools.database.can.formats.dbc_specifics import (
    DbcSpecifics as CantoolsDbcSpecifics,
)
from cantools.database.can.node import Node as CantoolsNode
from cantools.database.can.signal_group import SignalGroup as CantoolsSignalGroup
from cantools.database.namedsignalvalue import NamedSignalValue

from .client._helpers import dump_json, to_signal_fraction
from .protocols import (
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
    DBCSignal,
    DBCSignalGroup,
    DBCValueEntry,
    DBCValueTable,
    DBCVarType,
)

# CAN Extended Frame Format flag — bit 31 set to distinguish 29-bit extended
# IDs from 11-bit standard IDs in .dbc file format.
_CAN_EFF_FLAG = 0x80000000


def signal_to_json(signal: cantools.database.can.Signal) -> DBCSignal:
    """Convert a cantools Signal to JSON format."""

    # Validate byte order
    byte_order = signal.byte_order
    if byte_order not in ("little_endian", "big_endian"):
        raise ValueError(
            f"Unknown byte order {byte_order!r} for signal {signal.name!r}"
        )

    # cantools uses is_signed, we use "signed" field
    is_signed = signal.is_signed

    # cantools may return None for min/max, use reasonable defaults
    min_value = signal.minimum if signal.minimum is not None else 0.0
    max_value = signal.maximum if signal.maximum is not None else 0.0

    # Base signal fields common to all signal types. Numeric fields are
    # converted to Fraction to match DBCSignal's typed contract — the Agda
    # core works in ℚ and to_signal_fraction preserves decimal intent
    # (0.1 → 1/10) rather than the IEEE-754 binary approximation.
    #
    # ``receivers``: cantools exposes the trailing SG_ node list as
    # ``signal.receivers``. Its "no explicit receiver" sentinel is the
    # ``Vector__XXX`` placeholder, which we drop so the JSON wire list only
    # names real ECUs (matching the Agda validator's UnknownSignalReceiver
    # check against the BU_ table).
    receivers_raw = list(signal.receivers) if signal.receivers else []
    receivers_filtered = [r for r in receivers_raw if r != "Vector__XXX"]

    base_fields = {
        "name": signal.name,
        "startBit": signal.start,
        "length": signal.length,
        "byteOrder": byte_order,
        "signed": is_signed,
        "factor": to_signal_fraction(signal.scale),
        "offset": to_signal_fraction(signal.offset),
        "minimum": to_signal_fraction(min_value),
        "maximum": to_signal_fraction(max_value),
        "unit": signal.unit if signal.unit else "",
        "receivers": receivers_filtered,
    }

    # Handle multiplexing: check if signal has multiplexer_ids
    if signal.multiplexer_ids:
        multiplexor_name = signal.multiplexer_signal if signal.multiplexer_signal else "unknown"
        return cast(DBCSignal, {
            **base_fields,
            "multiplexor": multiplexor_name,
            "multiplex_values": list(signal.multiplexer_ids)
        })

    # Default: signal is always present
    return cast(DBCSignal, {
        **base_fields,
        "presence": "always"
    })


def message_to_json(message: cantools.database.can.Message) -> DBCMessage:
    """Convert a cantools Message to JSON format."""

    message_dict: DBCMessage = {
        "id": message.frame_id,
        "name": message.name,
        "dlc": message.length,
        "sender": message.senders[0] if message.senders else "",
        "signals": [signal_to_json(sig) for sig in message.signals]
    }

    # Add extended field if this is an extended frame (29-bit ID)
    if message.is_extended_frame:
        message_dict["extended"] = True

    return message_dict


def signal_group_to_json(
    group: CantoolsSignalGroup,
) -> DBCSignalGroup:
    """Flatten a cantools SignalGroup into the Agda wire format.

    cantools stores signal groups per-message (``message.signal_groups``);
    the Agda core expects a flat top-level list because signal-name
    uniqueness is enforced globally. ``repetitions`` is dropped — it is
    a DBC-text-format concern with no verifier-side semantics.
    """
    return {
        "name": group.name,
        "signals": list(group.signal_names),
    }


def _env_var_type_to_wire(env_type: int, name: str) -> DBCVarType:
    """Validate cantools' ``env_type`` (expected 0/1/2) as a wire VarType."""
    if env_type == 0:
        return 0
    if env_type == 1:
        return 1
    if env_type == 2:
        return 2
    raise ValueError(
        f"Unknown environment variable type {env_type!r} for {name!r}"
    )


def env_var_to_json(
    ev: CantoolsEnvironmentVariable,
) -> DBCEnvironmentVar:
    """Convert a cantools EnvironmentVariable to the Agda wire format.

    ``initial_value`` / ``minimum`` / ``maximum`` come back from cantools
    as ``int`` or ``float`` depending on the variable type; we convert
    through ``to_signal_fraction`` to preserve decimal intent the same
    way DBCSignal numeric fields do.
    """
    return {
        "name": ev.name,
        "varType": _env_var_type_to_wire(ev.env_type, ev.name),
        "initial": to_signal_fraction(ev.initial_value),
        "minimum": to_signal_fraction(ev.minimum),
        "maximum": to_signal_fraction(ev.maximum),
    }


def value_table_to_json(
    name: str, entries: dict[int, NamedSignalValue]
) -> DBCValueTable:
    """Convert a cantools value-table entry (dict) to the Agda wire format.

    cantools exposes ``db.dbc.value_tables`` as
    ``OrderedDict[str, dict[int, NamedSignalValue]]`` — the proxy is not
    JSON-serialisable but round-trips through ``str()`` to its human-readable
    name.  We iterate entries in insertion order to keep the Agda roundtrip
    deterministic (cantools preserves DBC source order).
    """
    wire_entries: list[DBCValueEntry] = [
        {"value": value, "description": str(description)}
        for value, description in entries.items()
    ]
    return {"name": name, "entries": wire_entries}


def _collect_signal_groups(
    db: CantoolsDatabase,
) -> list[DBCSignalGroup]:
    """Flatten ``msg.signal_groups`` across all messages.

    Iteration order: messages in DBC source order, then groups in per-message
    source order — matches cantools' ``Database.messages`` ordering.
    """
    groups: list[DBCSignalGroup] = []
    for msg in db.messages:
        for group in msg.signal_groups:
            groups.append(signal_group_to_json(group))
    return groups


# ---------------------------------------------------------------------------
# Tier 2: nodes / comments / attributes
# ---------------------------------------------------------------------------


def node_to_json(node: CantoolsNode) -> DBCNode:
    """Convert a cantools ``Node`` to the Agda wire format. Only the declared
    name survives; node-scope comments and attributes are emitted separately
    so that wire ordering matches the Agda ``List DBCComment`` / ``List
    DBCAttribute`` structure.
    """
    return {"name": node.name}


def _message_id_wire(msg: cantools.database.can.Message) -> tuple[int, bool]:
    """Return ``(id, extended)`` for a cantools ``Message``; ``extended``
    distinguishes 29-bit frames from 11-bit standard IDs on the wire."""
    return (msg.frame_id, bool(msg.is_extended_frame))


def _attach_extended(base: dict[str, object], extended: bool) -> None:
    """Attach ``extended: true`` only for 29-bit IDs — the Agda parser treats
    the field as optional, so omitting it for 11-bit IDs keeps the wire
    payload minimal and mirrors ``formatCANId`` in ``Formatter.agda``."""
    if extended:
        base["extended"] = True


def _comment_target_message(
    msg: cantools.database.can.Message,
) -> DBCCommentTarget:
    msg_id, extended = _message_id_wire(msg)
    target: dict[str, object] = {"kind": "message", "id": msg_id}
    _attach_extended(target, extended)
    return cast(DBCCommentTarget, target)


def _comment_target_signal(
    msg: cantools.database.can.Message, signal_name: str,
) -> DBCCommentTarget:
    msg_id, extended = _message_id_wire(msg)
    target: dict[str, object] = {
        "kind": "signal",
        "id": msg_id,
        "signal": signal_name,
    }
    _attach_extended(target, extended)
    return cast(DBCCommentTarget, target)


def _build_comments(db: CantoolsDatabase) -> list[DBCComment]:
    """Walk cantools' per-object ``.comment`` attrs to produce a single
    ordered list matching the Agda ``List DBCComment`` shape.

    Order: network (from ``db.buses[0].comment`` when present) → nodes →
    messages → signals (nested under messages) → environment variables.
    """
    comments: list[DBCComment] = []

    # Network-wide comment lives on a synthetic bus with empty name.
    if db.buses and db.buses[0].comment:
        comments.append({
            "target": {"kind": "network"},
            "text": db.buses[0].comment,
        })

    for node in db.nodes:
        if node.comment:
            comments.append({
                "target": {"kind": "node", "node": node.name},
                "text": node.comment,
            })

    for msg in db.messages:
        if msg.comment:
            comments.append({
                "target": _comment_target_message(msg),
                "text": msg.comment,
            })
        for signal in msg.signals:
            if signal.comment:
                comments.append({
                    "target": _comment_target_signal(msg, signal.name),
                    "text": signal.comment,
                })

    if db.dbc is not None:
        for ev in db.dbc.environment_variables.values():
            if ev.comment:
                comments.append({
                    "target": {"kind": "envVar", "envVar": ev.name},
                    "text": ev.comment,
                })

    return comments


# DBC wire vocabulary → Agda ``AttrScope`` (see ``AttrScope.agda``). ``None``
# encodes the network scope; ``BU_BO_REL_`` / ``BU_SG_REL_`` are the
# relational scopes introduced by ``BA_DEF_REL_``.
_CANTOOLS_KIND_TO_SCOPE: dict[str | None, AttrScope] = {
    None: "network",
    "BU_": "node",
    "BO_": "message",
    "SG_": "signal",
    "EV_": "envVar",
    "BU_BO_REL_": "nodeMsg",
    "BU_SG_REL_": "nodeSig",
}


def _cantools_kind_to_scope(kind: str | None) -> AttrScope:
    """Map cantools' ``AttributeDefinition.kind`` to the Agda ``AttrScope``
    vocabulary. An unrecognised kind is a converter bug, so we surface it
    as a ``ValueError`` at this boundary rather than silently emitting a
    wrong wire value.
    """
    scope = _CANTOOLS_KIND_TO_SCOPE.get(kind)
    if scope is None:
        raise ValueError(f"Unknown cantools attribute kind {kind!r}")
    return scope


def _attr_def_type(
    definition: CantoolsAttrDefinition,
) -> DBCAttrType:
    """Map a cantools ``AttributeDefinition`` to its ``DBCAttrType`` wire
    form. Numeric bounds for INT/HEX are passed through as integers; FLOAT
    bounds widen to ``Fraction`` to match the Agda ℚ domain.
    """
    type_name = definition.type_name
    if type_name == "INT":
        return {
            "kind": "int",
            "min": int(definition.minimum) if definition.minimum is not None else 0,
            "max": int(definition.maximum) if definition.maximum is not None else 0,
        }
    if type_name == "FLOAT":
        min_v = definition.minimum if definition.minimum is not None else 0.0
        max_v = definition.maximum if definition.maximum is not None else 0.0
        return {
            "kind": "float",
            "min": to_signal_fraction(min_v),
            "max": to_signal_fraction(max_v),
        }
    if type_name == "STRING":
        return {"kind": "string"}
    if type_name == "ENUM":
        return {"kind": "enum", "values": list(definition.choices or [])}
    if type_name == "HEX":
        return {
            "kind": "hex",
            "min": int(definition.minimum) if definition.minimum is not None else 0,
            "max": int(definition.maximum) if definition.maximum is not None else 0,
        }
    raise ValueError(
        f"Unknown attribute type_name {type_name!r} for {definition.name!r}"
    )


def _enum_index(
    definition: CantoolsAttrDefinition, value: object,
) -> int:
    """Resolve an ENUM value to its 0-based index.

    Defaults arrive as labels (str), assignments as int indices (cantools
    stores whichever form the DBC file used). Resolve both to the integer
    index the Agda ``AVEnum`` constructor demands; a label miss is a
    converter-level bug we surface as ``ValueError``.
    """
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    if isinstance(value, str):
        choices = list(definition.choices or [])
        if value not in choices:
            raise ValueError(
                f"Enum value {value!r} not in choices {choices!r}"
                + f" for attribute {definition.name!r}"
            )
        return choices.index(value)
    raise ValueError(
        f"Unexpected enum value {value!r} (type={type(value).__name__})"
        + f" for attribute {definition.name!r}"
    )


def _attr_value_wire(
    definition: CantoolsAttrDefinition, value: object,
) -> DBCAttrValue:
    """Dispatch on the declared type to build the correct ``DBCAttrValue``
    variant. Handlers differ only in the Python → wire coercion rule, so we
    funnel them through one function to keep the type dispatch colocated
    with ``_attr_def_type``.
    """
    type_name = definition.type_name
    if type_name == "INT":
        return {"kind": "int", "value": int(cast(int | float, value))}
    if type_name == "FLOAT":
        return {
            "kind": "float",
            "value": to_signal_fraction(cast(float | int | Fraction, value)),
        }
    if type_name == "STRING":
        return {"kind": "string", "value": str(value)}
    if type_name == "ENUM":
        return {"kind": "enum", "value": _enum_index(definition, value)}
    if type_name == "HEX":
        return {"kind": "hex", "value": int(cast(int | float, value))}
    raise ValueError(
        f"Unknown attribute type_name {type_name!r} for {definition.name!r}"
    )


def _attribute_def_entry(
    definition: CantoolsAttrDefinition,
) -> DBCAttrDef:
    return {
        "kind": "definition",
        "name": definition.name,
        "scope": _cantools_kind_to_scope(definition.kind),
        "attrType": _attr_def_type(definition),
    }


def _attribute_default_entry(
    definition: CantoolsAttrDefinition,
) -> DBCAttrDefault | None:
    """Emit a ``DBCAttrDefault`` only when cantools recorded a default. An
    absent default (``None``) differs from a declared empty string or zero:
    the validator's ``checkDuplicateAttributeNames`` check uses this
    distinction to avoid flagging synthetic defaults.
    """
    if definition.default_value is None:
        return None
    return {
        "kind": "default",
        "name": definition.name,
        "value": _attr_value_wire(definition, definition.default_value),
    }


def _attr_target_network() -> DBCAttrTarget:
    return {"kind": "network"}


def _attr_target_node(node_name: str) -> DBCAttrTarget:
    return {"kind": "node", "node": node_name}


def _attr_target_message(msg: cantools.database.can.Message) -> DBCAttrTarget:
    msg_id, extended = _message_id_wire(msg)
    target: dict[str, object] = {"kind": "message", "id": msg_id}
    _attach_extended(target, extended)
    return cast(DBCAttrTarget, target)


def _attr_target_signal(
    msg: cantools.database.can.Message, signal_name: str,
) -> DBCAttrTarget:
    msg_id, extended = _message_id_wire(msg)
    target: dict[str, object] = {
        "kind": "signal", "id": msg_id, "signal": signal_name,
    }
    _attach_extended(target, extended)
    return cast(DBCAttrTarget, target)


def _attr_target_envvar(ev_name: str) -> DBCAttrTarget:
    return {"kind": "envVar", "envVar": ev_name}


def _attr_target_node_msg(
    node_name: str, msg: cantools.database.can.Message,
) -> DBCAttrTarget:
    msg_id, extended = _message_id_wire(msg)
    target: dict[str, object] = {
        "kind": "nodeMsg", "node": node_name, "id": msg_id,
    }
    _attach_extended(target, extended)
    return cast(DBCAttrTarget, target)


def _attr_target_node_sig(
    node_name: str, msg: cantools.database.can.Message, signal_name: str,
) -> DBCAttrTarget:
    msg_id, extended = _message_id_wire(msg)
    target: dict[str, object] = {
        "kind": "nodeSig",
        "node": node_name,
        "id": msg_id,
        "signal": signal_name,
    }
    _attach_extended(target, extended)
    return cast(DBCAttrTarget, target)


def _make_assignment(
    definition: CantoolsAttrDefinition,
    target: DBCAttrTarget,
    attr: CantoolsAttribute,
) -> DBCAttrAssign:
    return {
        "kind": "assignment",
        "name": definition.name,
        "target": target,
        "value": _attr_value_wire(definition, attr.value),
    }


def _collect_network_assignments(
    specifics: CantoolsDbcSpecifics,
) -> list[DBCAttrAssign]:
    return [
        _make_assignment(attr.definition, _attr_target_network(), attr)
        for attr in specifics.attributes.values()
    ]


def _collect_node_assignments(db: CantoolsDatabase) -> list[DBCAttrAssign]:
    result: list[DBCAttrAssign] = []
    for node in db.nodes:
        if node.dbc is None:
            continue
        for attr in node.dbc.attributes.values():
            result.append(_make_assignment(
                attr.definition, _attr_target_node(node.name), attr,
            ))
    return result


def _collect_message_and_signal_assignments(
    db: CantoolsDatabase,
) -> list[DBCAttrAssign]:
    result: list[DBCAttrAssign] = []
    for msg in db.messages:
        if msg.dbc is None:
            continue
        for attr in msg.dbc.attributes.values():
            result.append(_make_assignment(
                attr.definition, _attr_target_message(msg), attr,
            ))
        for signal in msg.signals:
            if signal.dbc is None:
                continue
            for attr in signal.dbc.attributes.values():
                result.append(_make_assignment(
                    attr.definition,
                    _attr_target_signal(msg, signal.name),
                    attr,
                ))
    return result


def _collect_envvar_assignments(
    specifics: CantoolsDbcSpecifics,
) -> list[DBCAttrAssign]:
    result: list[DBCAttrAssign] = []
    for ev in specifics.environment_variables.values():
        if ev.dbc is None:
            continue
        for attr in ev.dbc.attributes.values():
            result.append(_make_assignment(
                attr.definition, _attr_target_envvar(ev.name), attr,
            ))
    return result


def _collect_plain_assignments(
    db: CantoolsDatabase,
) -> list[DBCAttrAssign]:
    """Gather ``BA_`` assignments from network + per-node/msg/sig/envvar.
    Emission order matches Agda ``List DBCAttribute``: network, then nodes
    in declared order, then messages (per-message assignments), then signals
    (nested), then environment variables. Scope mix is intentional — the
    Agda list is heterogeneous by design.
    """
    specifics = db.dbc
    if specifics is None:
        return []
    return [
        *_collect_network_assignments(specifics),
        *_collect_node_assignments(db),
        *_collect_message_and_signal_assignments(db),
        *_collect_envvar_assignments(specifics),
    ]


def _collect_nodemsg_from_scope(
    scopes: dict[str, object], msg: cantools.database.can.Message,
) -> list[DBCAttrAssign]:
    """Expand the ``"node"`` bucket at the top of a ``BA_REL_`` scope map."""
    node_bucket = cast(
        dict[str, dict[str, CantoolsAttribute]] | None,
        scopes.get("node"),
    )
    if not node_bucket:
        return []
    return [
        _make_assignment(
            attr.definition, _attr_target_node_msg(node_name, msg), attr,
        )
        for node_name, node_attrs in node_bucket.items()
        for attr in node_attrs.values()
    ]


def _collect_nodesig_from_scope(
    scopes: dict[str, object], msg: cantools.database.can.Message,
) -> list[DBCAttrAssign]:
    """Expand the nested ``{"signal": {sig: {"node": {node: attr}}}}``
    bucket inside a ``BA_REL_`` scope map."""
    signal_bucket = cast(
        dict[str, dict[str, dict[str, dict[str, CantoolsAttribute]]]] | None,
        scopes.get("signal"),
    )
    if not signal_bucket:
        return []
    result: list[DBCAttrAssign] = []
    for signal_name, sig_scopes in signal_bucket.items():
        sig_node_bucket = sig_scopes.get("node") or {}
        for node_name, node_attrs in sig_node_bucket.items():
            for attr in node_attrs.values():
                result.append(_make_assignment(
                    attr.definition,
                    _attr_target_node_sig(node_name, msg, signal_name),
                    attr,
                ))
    return result


def _collect_rel_assignments(
    db: CantoolsDatabase,
) -> list[DBCAttrAssign]:
    """Walk ``db.dbc.attributes_rel`` — cantools' ``BA_REL_`` container with
    shape ``{msg_id: {"node": {node: {attr: Attribute}},
    "signal": {sig: {"node": {node: {attr: Attribute}}}}}}``. We flatten to
    flat ``nodeMsg`` / ``nodeSig`` assignments matching the Agda
    ``ATgtNodeMsg`` / ``ATgtNodeSig`` constructors.

    Lookup by ``frame_id`` finds the matching message so we can preserve
    the extended-frame flag on the wire; an ``attributes_rel`` entry with
    no corresponding message is a cantools-internal invariant violation,
    so we raise rather than silently dropping.
    """
    specifics = db.dbc
    if specifics is None:
        return []

    messages_by_id: dict[int, cantools.database.can.Message] = {
        m.frame_id: m for m in db.messages
    }

    assigns: list[DBCAttrAssign] = []
    for frame_id, scopes in specifics.attributes_rel.items():
        msg = messages_by_id.get(frame_id)
        if msg is None:
            raise ValueError(
                f"attributes_rel references unknown message id {frame_id}"
            )
        assigns.extend(_collect_nodemsg_from_scope(scopes, msg))
        assigns.extend(_collect_nodesig_from_scope(scopes, msg))

    return assigns


def _build_attributes(db: CantoolsDatabase) -> list[DBCAttribute]:
    """Emit the flat ``List DBCAttribute`` expected by the Agda core.

    Output order: all definitions first (plain then relational), then all
    defaults in the same order, then assignments. The Agda parser only
    cares about well-formedness, not ordering, but the Python-side test
    fixture compares list equality — so ordering is pinned here and kept
    stable across cantools versions via explicit iteration rather than
    dict-view copies.
    """
    attributes: list[DBCAttribute] = []
    specifics = db.dbc
    if specifics is None:
        return attributes

    all_defs: list[CantoolsAttrDefinition] = [
        *specifics.attribute_definitions.values(),
        *(specifics.attribute_definitions_rel or {}).values(),
    ]

    for definition in all_defs:
        attributes.append(_attribute_def_entry(definition))

    for definition in all_defs:
        default_entry = _attribute_default_entry(definition)
        if default_entry is not None:
            attributes.append(default_entry)

    attributes.extend(_collect_plain_assignments(db))
    attributes.extend(_collect_rel_assignments(db))

    return attributes


def dbc_to_json(dbc_path: str | Path) -> DBCDefinition:
    """Convert a .dbc file to JSON format.

    Args:
        dbc_path: Path to the .dbc file

    Returns:
        DBC definition in the format expected by Aletheia.DBC.JSONParser

    Raises:
        OSError: If the file cannot be read.
        ValueError: If the file is not a valid DBC.
    """
    # Load DBC file using cantools
    try:
        db = cantools.database.load_file(str(dbc_path))
    except OSError:
        raise
    except Exception as exc:
        raise ValueError(f"Failed to parse DBC file '{dbc_path}': {exc}") from exc

    specifics = db.dbc
    environment_vars: dict[str, CantoolsEnvironmentVariable] = (
        specifics.environment_variables if specifics is not None else {}
    )
    value_tables: dict[str, dict[int, NamedSignalValue]] = (
        specifics.value_tables if specifics is not None else {}
    )

    dbc_def: DBCDefinition = {
        "version": db.version if db.version else "1.0",
        "messages": [message_to_json(msg) for msg in db.messages],
        "signalGroups": _collect_signal_groups(db),
        "environmentVars": [env_var_to_json(ev) for ev in environment_vars.values()],
        "valueTables": [
            value_table_to_json(name, entries)
            for name, entries in value_tables.items()
        ],
        "nodes": [node_to_json(n) for n in db.nodes],
        "comments": _build_comments(db),
        "attributes": _build_attributes(db),
    }
    return dbc_def


def _format_number(value: float | Fraction) -> str:
    """Format a numeric signal field for DBC output.

    Fractions exactly representable as integers emit as ``"int"``; other
    Fractions emit as a 15-digit decimal via float conversion (DBC's text
    format is decimal-only, so exact rational preservation is impossible
    at this layer — this matches cantools' .dbc output convention).
    """
    if isinstance(value, Fraction):
        if value.denominator == 1:
            return str(value.numerator)
        return f"{float(value):.15g}"
    if value.is_integer():
        return str(int(value))
    return f"{value:.15g}"


def _signal_to_dbc_line(
    signal: DBCSignal,
    mux_signal_names: set[str] | None = None,
) -> str:
    """Format a single signal as a DBC SG_ line."""
    name = signal["name"]
    start_bit = signal["startBit"]
    length = signal["length"]

    # Byte order: 1 = little_endian, 0 = big_endian
    bo = "1" if signal["byteOrder"] == "little_endian" else "0"

    # Sign: + = unsigned, - = signed
    sign = "-" if signal["signed"] else "+"

    factor = _format_number(signal["factor"])
    offset = _format_number(signal["offset"])
    minimum = _format_number(signal["minimum"])
    maximum = _format_number(signal["maximum"])
    unit = signal["unit"]

    # Multiplexing indicator: M for multiplexor, m<val> for multiplexed
    # Standard DBC format only supports a single mux value in the SG_ line;
    # extended mux (SG_MUL_VAL_) is not emitted here. Take the first value.
    mux_indicator = ""
    if "multiplexor" in signal:
        mux_vals = signal["multiplex_values"]
        mux_indicator = f" m{mux_vals[0]}"
    elif mux_signal_names and name in mux_signal_names:
        mux_indicator = " M"

    # Trailing receiver list. Vector__XXX is the DBC convention for "no
    # specific receiver", used when the per-signal receivers field is empty.
    receivers_text = ",".join(signal.get("receivers") or ()) or "Vector__XXX"
    return (
        f" SG_ {name}{mux_indicator} : "
        f"{start_bit}|{length}@{bo}{sign} "
        f"({factor},{offset}) "
        f"[{minimum}|{maximum}] "
        f'"{unit}" {receivers_text}'
    )


def dbc_to_text(dbc: DBCDefinition) -> str:
    """Convert a DBC JSON dict to .dbc file text format.

    Args:
        dbc: DBC definition dict (as returned by ``dbc_to_json()``
             or ``AletheiaClient.format_dbc()``).

    Returns:
        String containing the .dbc file content.
    """
    lines: list[str] = []

    # VERSION
    version = dbc.get("version", "")
    lines.append(f'VERSION "{version}"')
    lines.append("")

    # NS_ (stub)
    lines.append("NS_ :")
    lines.append("")

    # BS_ (stub)
    lines.append("BS_:")
    lines.append("")

    # BU_ — collect unique senders from messages
    senders: list[str] = []
    seen_senders: set[str] = set()
    for msg in dbc["messages"]:
        sender = msg.get("sender", "")
        if sender and sender not in seen_senders:
            senders.append(sender)
            seen_senders.add(sender)
    lines.append("BU_: " + " ".join(senders))
    lines.append("")

    # Messages
    for msg in dbc["messages"]:
        msg_id = msg["id"]
        if msg.get("extended"):
            msg_id = msg_id | _CAN_EFF_FLAG
        msg_name = msg["name"]
        dlc = msg["dlc"]
        sender = msg.get("sender", "")

        lines.append(f"BO_ {msg_id} {msg_name}: {dlc} {sender}")

        # Collect multiplexor signal names referenced by multiplexed signals
        mux_signal_names: set[str] = set()
        for signal in msg.get("signals", []):
            if "multiplexor" in signal:
                mux_signal_names.add(signal["multiplexor"])

        for signal in msg.get("signals", []):
            lines.append(_signal_to_dbc_line(signal, mux_signal_names))

        lines.append("")

    return "\n".join(lines)


def convert_dbc_file(dbc_path: str | Path, output_path: str | Path | None = None) -> str:
    """Convert a .dbc file to JSON and optionally write to file.

    Args:
        dbc_path: Path to the .dbc file
        output_path: Optional path to write JSON output. If None, returns JSON string.

    Returns:
        JSON string representation of the DBC file
    """
    dbc_json = dbc_to_json(dbc_path)
    json_str = dump_json(dbc_json, indent=2)

    if output_path:
        _ = Path(output_path).write_text(json_str, encoding='utf-8')

    return json_str
