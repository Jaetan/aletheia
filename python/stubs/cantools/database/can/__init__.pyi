"""Type stubs for cantools.database.can module.

Only covers the subset of the cantools API that Aletheia's ``dbc_converter``
module needs. cantools ships ``py.typed`` but several DBC-metadata types
(``SignalGroup``, ``EnvironmentVariable``, ``DbcSpecifics``) have untyped
property accessors, so pyright hits ``Unknown`` without these local stubs.
"""

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
    multiplexer_ids: list[int] | None
    multiplexer_signal: str | None


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


class Message:
    """CAN message definition from a DBC file."""
    frame_id: int
    name: str
    length: int
    senders: list[str]
    signals: list[Signal]
    is_extended_frame: bool
    signal_groups: list[SignalGroup]


class DbcSpecifics:
    """DBC-specific metadata attached to ``Database.dbc``.

    ``value_tables`` descriptions are wrapped in a ``NamedSignalValue`` proxy
    that is not JSON-serialisable but round-trips through ``str()`` — see
    ``value_table_to_json``.
    """
    environment_variables: dict[str, EnvironmentVariable]
    value_tables: dict[str, dict[int, NamedSignalValue]]


class Database:
    """CAN database loaded from a DBC file."""
    version: str | None
    messages: list[Message]
    dbc: DbcSpecifics | None
