"""Type definitions for structured data

Defines TypedDict classes and Enums for well-known structures.
This provides better type safety and IDE support.
"""

from __future__ import annotations

from enum import Enum
from typing import TypedDict, NotRequired, Union, Literal


class ByteOrder(str, Enum):
    """CAN signal byte order"""
    LITTLE_ENDIAN = "little_endian"
    BIG_ENDIAN = "big_endian"


class SignalPresence(str, Enum):
    """Signal presence in CAN message"""
    ALWAYS = "always"
    # Multiplexed signals use dictionary format, not enum


class ResponseStatus(str, Enum):
    """Response status from Aletheia binary"""
    SUCCESS = "success"
    ERROR = "error"
    ACK = "ack"
    VIOLATED = "violated"
    COMPLETE = "complete"


class ComparisonOp(str, Enum):
    """Comparison operators for signal predicates"""
    EQ = "EQ"  # Equals
    LT = "LT"  # Less than
    GT = "GT"  # Greater than
    LE = "LE"  # Less than or equal
    GE = "GE"  # Greater than or equal


# ============================================================================
# DBC Structure Types
# ============================================================================

class DBCSignalAlways(TypedDict):
    """DBC signal that is always present"""
    name: str
    startBit: int
    length: int
    byteOrder: str  # "little_endian" | "big_endian"
    signed: bool
    factor: float
    offset: float
    minimum: float
    maximum: float
    unit: str
    presence: str  # "always"


class DBCSignalMultiplexed(TypedDict):
    """DBC signal that is conditionally present (multiplexed)"""
    name: str
    startBit: int
    length: int
    byteOrder: str  # "little_endian" | "big_endian"
    signed: bool
    factor: float
    offset: float
    minimum: float
    maximum: float
    unit: str
    multiplexor: str  # Name of multiplexor signal
    multiplex_value: int  # Value of multiplexor when this signal is present


# Union type for all signal types
DBCSignal = Union[DBCSignalAlways, DBCSignalMultiplexed]


class DBCMessage(TypedDict):
    """DBC message definition structure"""
    id: int
    name: str
    dlc: int
    sender: str
    signals: list[DBCSignal]
    extended: NotRequired[bool]  # Optional: true for 29-bit, false/absent for 11-bit


class DBCDefinition(TypedDict):
    """Complete DBC file structure"""
    version: str
    messages: list[DBCMessage]


# ============================================================================
# LTL Formula Types (Predicates)
# ============================================================================

class CompareFormula(TypedDict):
    """Comparison predicate: signal op value"""
    type: Literal["compare"]
    signal: str
    op: str  # "EQ" | "LT" | "GT" | "LE" | "GE"
    value: float


class BetweenFormula(TypedDict):
    """Between predicate: min <= signal <= max"""
    type: Literal["between"]
    signal: str
    min: float
    max: float


class ChangedByFormula(TypedDict):
    """Changed by predicate: signal changed by delta"""
    type: Literal["changed_by"]
    signal: str
    delta: float


class AndFormula(TypedDict):
    """Logical AND: left && right"""
    type: Literal["and"]
    left: 'LTLFormula'
    right: 'LTLFormula'


class OrFormula(TypedDict):
    """Logical OR: left || right"""
    type: Literal["or"]
    left: 'LTLFormula'
    right: 'LTLFormula'


class NotFormula(TypedDict):
    """Logical NOT: !formula"""
    type: Literal["not"]
    formula: 'LTLFormula'


# ============================================================================
# LTL Formula Types (Temporal Operators)
# ============================================================================

class AlwaysFormula(TypedDict):
    """Always (globally): G(formula)"""
    type: Literal["always"]
    formula: 'LTLFormula'


class EventuallyFormula(TypedDict):
    """Eventually (finally): F(formula)"""
    type: Literal["eventually"]
    formula: 'LTLFormula'


class NeverFormula(TypedDict):
    """Never: G(!formula)"""
    type: Literal["never"]
    formula: 'LTLFormula'


class EventuallyWithinFormula(TypedDict):
    """Eventually within time bound: F_{<=t}(formula)"""
    type: Literal["eventually_within"]
    time_ms: int
    formula: 'LTLFormula'


class AlwaysWithinFormula(TypedDict):
    """Always within time bound: G_{<=t}(formula)"""
    type: Literal["always_within"]
    time_ms: int
    formula: 'LTLFormula'


class ImpliesFormula(TypedDict):
    """Logical implication: antecedent -> consequent"""
    type: Literal["implies"]
    antecedent: 'LTLFormula'
    consequent: 'LTLFormula'


class UntilFormula(TypedDict):
    """Temporal until: left U right"""
    type: Literal["until"]
    left: 'LTLFormula'
    right: 'LTLFormula'


# Union type for all LTL formulas
LTLFormula = Union[
    CompareFormula,
    BetweenFormula,
    ChangedByFormula,
    AndFormula,
    OrFormula,
    NotFormula,
    AlwaysFormula,
    EventuallyFormula,
    NeverFormula,
    EventuallyWithinFormula,
    AlwaysWithinFormula,
    ImpliesFormula,
    UntilFormula,
]


# ============================================================================
# Command and Response Types
# ============================================================================

class ParseDBCCommand(TypedDict):
    """Parse DBC file command"""
    type: str  # "command"
    command: str  # "parseDBC"
    dbc: DBCDefinition


class SetPropertiesCommand(TypedDict):
    """Set LTL properties command"""
    type: str  # "command"
    command: str  # "setProperties"
    properties: list[LTLFormula]


class StartStreamCommand(TypedDict):
    """Start streaming command"""
    type: str  # "command"
    command: str  # "startStream"


class EndStreamCommand(TypedDict):
    """End streaming command"""
    type: str  # "command"
    command: str  # "endStream"


class DataFrame(TypedDict):
    """CAN data frame"""
    type: str  # "data"
    timestamp: int
    id: int
    data: list[int]


# Union type for all commands
Command = Union[
    ParseDBCCommand,
    SetPropertiesCommand,
    StartStreamCommand,
    EndStreamCommand,
    DataFrame,
]


class SuccessResponse(TypedDict):
    """Success response"""
    status: ResponseStatus  # ResponseStatus.SUCCESS
    message: str


class ErrorResponse(TypedDict):
    """Error response"""
    status: ResponseStatus  # ResponseStatus.ERROR
    message: str


class AckResponse(TypedDict):
    """Acknowledgment response"""
    status: ResponseStatus  # ResponseStatus.ACK


class PropertyViolationResponse(TypedDict):
    """Property violation response"""
    status: ResponseStatus  # ResponseStatus.VIOLATED
    type: str  # "property"
    property_id: int
    timestamp: int
    message: NotRequired[str]


class CompleteResponse(TypedDict):
    """Stream complete response"""
    status: ResponseStatus  # ResponseStatus.COMPLETE


# Union type for all responses
Response = Union[
    SuccessResponse,
    ErrorResponse,
    AckResponse,
    PropertyViolationResponse,
    CompleteResponse,
]
