"""Type stubs for cantools.database.can module.

Only covers the subset of the cantools API that Aletheia's ``dbc_converter``
module needs. cantools ships ``py.typed`` but several DBC-metadata types
(``SignalGroup``, ``EnvironmentVariable``, ``DbcSpecifics``, ``Node``,
``Attribute``, ``AttributeDefinition``, ``Bus``) have untyped property
accessors, so pyright hits ``Unknown`` without these local stubs.
"""

from collections import OrderedDict
from typing import Literal

from cantools.database.namedsignalvalue import NamedSignalValue as NamedSignalValue


class Signal:
    """CAN signal definition from a DBC file."""
    name: str
    start: int
    length: int
    byte_order: Literal["little_endian", "big_endian"]
    is_signed: bool
    scale: float
    offset: float
    minimum: float | None
    maximum: float | None
    unit: str | None
    comment: str | None
    receivers: list[str]
    multiplexer_ids: list[int] | None
    multiplexer_signal: str | None
    dbc: "DbcSpecifics | None"


class SignalGroup:
    """DBC ``SIG_GROUP_`` entry attached per-message.

    Only fields Aletheia consumes. cantools also exposes ``repetitions`` and
    ``message`` back-pointer, which we intentionally drop on the wire.
    """
    name: str
    signal_names: list[str]


class EnvironmentVariable:
    """DBC ``EV_`` entry, held on ``DbcSpecifics.environment_variables``.

    ``env_type`` follows the DBC wire vocabulary: 0=int, 1=float, 2=string;
    cantools does not narrow the attribute type, so it is declared as ``int``
    here and validated by ``_env_var_type_to_wire`` at the boundary.
    """
    name: str
    env_type: int
    initial_value: float | int
    minimum: float | int
    maximum: float | int
    comment: str | None
    dbc: "DbcSpecifics | None"


class Message:
    """CAN message definition from a DBC file."""
    frame_id: int
    name: str
    length: int
    senders: list[str]
    signals: list[Signal]
    is_extended_frame: bool
    signal_groups: list[SignalGroup]
    comment: str | None
    dbc: "DbcSpecifics | None"


class Node:
    """DBC ``BU_`` node entry."""
    name: str
    comment: str | None
    dbc: "DbcSpecifics | None"


class Bus:
    """DBC bus entry. cantools synthesises a bare ``Bus`` instance with an
    empty ``name`` to carry the network-wide ``CM_ "..."`` comment.
    """
    name: str
    comment: str | None


class AttributeDefinition:
    """DBC ``BA_DEF_`` / ``BA_DEF_REL_`` entry.

    ``kind`` encodes the scope exactly as it appears in the DBC keyword:
    ``None`` → network, ``"BU_"`` → node, ``"BO_"`` → message, ``"SG_"`` →
    signal, ``"EV_"`` → envVar, ``"BU_BO_REL_"`` → nodeMsg,
    ``"BU_SG_REL_"`` → nodeSig. ``type_name`` is the raw DBC type keyword
    (``"INT"``/``"FLOAT"``/``"STRING"``/``"ENUM"``/``"HEX"``).
    """
    name: str
    type_name: str
    kind: str | None
    minimum: float | int | None
    maximum: float | int | None
    choices: list[str] | None
    default_value: float | int | str | None


class Attribute:
    """DBC ``BA_`` / ``BA_REL_`` concrete value assignment."""
    name: str
    value: float | int | str
    definition: AttributeDefinition


class DbcSpecifics:
    """DBC-specific metadata attached to ``Database.dbc``.

    ``value_tables`` descriptions are wrapped in a ``NamedSignalValue`` proxy
    that is not JSON-serialisable but round-trips through ``str()`` — see
    ``value_table_to_json``. ``attributes_rel`` is a nested OrderedDict of
    shape ``{msg_id: {"node": {node: {attr: Attribute}}, "signal": {sig:
    {"node": {node: {attr: Attribute}}}}}}`` holding ``BA_REL_`` values.
    """
    environment_variables: dict[str, EnvironmentVariable]
    value_tables: dict[str, dict[int, NamedSignalValue]]
    attribute_definitions: OrderedDict[str, AttributeDefinition]
    attribute_definitions_rel: OrderedDict[str, AttributeDefinition] | None
    attributes: OrderedDict[str, Attribute]
    attributes_rel: OrderedDict[int, dict[str, object]]


class Database:
    """CAN database loaded from a DBC file."""
    version: str | None
    messages: list[Message]
    nodes: list[Node]
    buses: list[Bus]
    dbc: DbcSpecifics | None
