"""Type definitions for structured data

Defines TypedDict classes and Enums for well-known structures.
This provides better type safety and IDE support.
"""

from __future__ import annotations

from enum import Enum
from typing import TypedDict, NotRequired, Literal


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
    VIOLATED = "violation"  # Note: binary sends "violation" not "violated"
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
DBCSignal = DBCSignalAlways | DBCSignalMultiplexed


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


class MetricEventuallyFormula(TypedDict):
    """Metric Eventually: F_{<=t}(formula)"""
    type: Literal["metricEventually"]
    time_ms: int
    formula: 'LTLFormula'


class MetricAlwaysFormula(TypedDict):
    """Metric Always: G_{<=t}(formula)"""
    type: Literal["metricAlways"]
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


class ReleaseFormula(TypedDict):
    """Temporal release: left R right (dual of until)"""
    type: Literal["release"]
    left: 'LTLFormula'
    right: 'LTLFormula'


class MetricUntilFormula(TypedDict):
    """Metric Until: left U_{<=t} right"""
    type: Literal["metricUntil"]
    time_ms: int
    left: 'LTLFormula'
    right: 'LTLFormula'


class MetricReleaseFormula(TypedDict):
    """Metric Release: left R_{<=t} right"""
    type: Literal["metricRelease"]
    time_ms: int
    left: 'LTLFormula'
    right: 'LTLFormula'


# Union type for all LTL formulas
LTLFormula = (
    CompareFormula |
    BetweenFormula |
    ChangedByFormula |
    AndFormula |
    OrFormula |
    NotFormula |
    AlwaysFormula |
    EventuallyFormula |
    NeverFormula |
    MetricEventuallyFormula |
    MetricAlwaysFormula |
    ImpliesFormula |
    UntilFormula |
    ReleaseFormula |
    MetricUntilFormula |
    MetricReleaseFormula
)


# ============================================================================
# Signal Operation Types
# ============================================================================

class RationalNumber(TypedDict):
    """Rational number representation from Agda"""
    numerator: int
    denominator: int


class SignalValue(TypedDict):
    """Signal name-value pair for encoding"""
    name: str
    value: float


class SignalError(TypedDict):
    """Signal name-error pair for extraction errors"""
    name: str
    error: str


# ============================================================================
# Command and Response Types
# ============================================================================

class ParseDBCCommand(TypedDict):
    """Parse DBC file command"""
    type: Literal["command"]
    command: Literal["parseDBC"]
    dbc: DBCDefinition


class SetPropertiesCommand(TypedDict):
    """Set LTL properties command"""
    type: Literal["command"]
    command: Literal["setProperties"]
    properties: list[LTLFormula]


class StartStreamCommand(TypedDict):
    """Start streaming command"""
    type: Literal["command"]
    command: Literal["startStream"]


class EndStreamCommand(TypedDict):
    """End streaming command"""
    type: Literal["command"]
    command: Literal["endStream"]


class BuildFrameCommand(TypedDict):
    """Build CAN frame from signal values"""
    type: Literal["command"]
    command: Literal["buildFrame"]
    canId: int
    signals: list[SignalValue]


class ExtractSignalsCommand(TypedDict):
    """Extract all signals from CAN frame"""
    type: Literal["command"]
    command: Literal["extractAllSignals"]
    canId: int
    data: list[int]


class UpdateFrameCommand(TypedDict):
    """Update signals in existing CAN frame"""
    type: Literal["command"]
    command: Literal["updateFrame"]
    canId: int
    frame: list[int]
    signals: list[SignalValue]


class DataFrame(TypedDict):
    """CAN data frame"""
    type: Literal["data"]
    timestamp: int
    id: int
    data: list[int]


# Union type for all commands
Command = (
    ParseDBCCommand |
    SetPropertiesCommand |
    StartStreamCommand |
    EndStreamCommand |
    BuildFrameCommand |
    ExtractSignalsCommand |
    UpdateFrameCommand |
    DataFrame
)


class SuccessResponse(TypedDict):
    """Success response"""
    status: ResponseStatus  # ResponseStatus.SUCCESS
    message: NotRequired[str]  # Optional message field


class ErrorResponse(TypedDict):
    """Error response"""
    status: ResponseStatus  # ResponseStatus.ERROR
    message: str


class AckResponse(TypedDict):
    """Acknowledgment response"""
    status: ResponseStatus  # ResponseStatus.ACK


class PropertyViolationResponse(TypedDict):
    """Property violation response"""
    status: Literal["violation"]  # Binary sends "violation"
    type: Literal["property"]
    property_index: RationalNumber
    timestamp: RationalNumber
    reason: NotRequired[str]  # Optional reason field from binary


class CompleteResponse(TypedDict):
    """Stream complete response"""
    status: ResponseStatus  # ResponseStatus.COMPLETE


class BuildFrameResponse(TypedDict):
    """Response from buildFrame command"""
    status: Literal["success"]
    frame: list[int]


class ExtractSignalsResponse(TypedDict):
    """Response from extractAllSignals command"""
    status: Literal["success"]
    values: list[SignalValue]
    errors: list[SignalError]
    absent: list[str]


class UpdateFrameResponse(TypedDict):
    """Response from updateFrame command"""
    status: Literal["success"]
    frame: list[int]


# Union type for all responses
Response = (
    SuccessResponse |
    ErrorResponse |
    AckResponse |
    PropertyViolationResponse |
    CompleteResponse |
    BuildFrameResponse |
    ExtractSignalsResponse |
    UpdateFrameResponse
)
