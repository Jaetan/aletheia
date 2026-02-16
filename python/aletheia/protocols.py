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


class PredicateType(str, Enum):
    """Signal predicate types matching Agda JSON schema"""
    EQUALS = "equals"
    LESS_THAN = "lessThan"
    GREATER_THAN = "greaterThan"
    LESS_THAN_OR_EQUAL = "lessThanOrEqual"
    GREATER_THAN_OR_EQUAL = "greaterThanOrEqual"
    BETWEEN = "between"
    CHANGED_BY = "changedBy"


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
# LTL Formula Types - Agda-compatible JSON schema
# ============================================================================
# All formulas use "operator" key (not "type").
# Predicates use {"operator": "atomic", "predicate": {...}} format.
# Time bounds use "timebound" key (not "time_ms").
# "never" and "implies" are desugared by Python before sending to Agda.

# -- Signal Predicates (inside "predicate" object) --

class EqualsPredicate(TypedDict):
    """Equals predicate: signal == value"""
    predicate: Literal["equals"]
    signal: str
    value: float


class LessThanPredicate(TypedDict):
    """LessThan predicate: signal < value"""
    predicate: Literal["lessThan"]
    signal: str
    value: float


class GreaterThanPredicate(TypedDict):
    """GreaterThan predicate: signal > value"""
    predicate: Literal["greaterThan"]
    signal: str
    value: float


class LessThanOrEqualPredicate(TypedDict):
    """LessThanOrEqual predicate: signal <= value"""
    predicate: Literal["lessThanOrEqual"]
    signal: str
    value: float


class GreaterThanOrEqualPredicate(TypedDict):
    """GreaterThanOrEqual predicate: signal >= value"""
    predicate: Literal["greaterThanOrEqual"]
    signal: str
    value: float


class BetweenPredicate(TypedDict):
    """Between predicate: min <= signal <= max"""
    predicate: Literal["between"]
    signal: str
    min: float
    max: float


class ChangedByPredicate(TypedDict):
    """ChangedBy predicate: |signal_now - signal_prev| <= delta"""
    predicate: Literal["changedBy"]
    signal: str
    delta: float


SignalPredicate = (
    EqualsPredicate |
    LessThanPredicate |
    GreaterThanPredicate |
    LessThanOrEqualPredicate |
    GreaterThanOrEqualPredicate |
    BetweenPredicate |
    ChangedByPredicate
)


# -- LTL Formula Types (using "operator" key) --

class AtomicFormula(TypedDict):
    """Atomic formula wrapping a signal predicate"""
    operator: Literal["atomic"]
    predicate: SignalPredicate


class AndFormula(TypedDict):
    """Logical AND: left && right"""
    operator: Literal["and"]
    left: 'LTLFormula'
    right: 'LTLFormula'


class OrFormula(TypedDict):
    """Logical OR: left || right"""
    operator: Literal["or"]
    left: 'LTLFormula'
    right: 'LTLFormula'


class NotFormula(TypedDict):
    """Logical NOT: !formula"""
    operator: Literal["not"]
    formula: 'LTLFormula'


class AlwaysFormula(TypedDict):
    """Always (globally): G(formula)"""
    operator: Literal["always"]
    formula: 'LTLFormula'


class EventuallyFormula(TypedDict):
    """Eventually (finally): F(formula)"""
    operator: Literal["eventually"]
    formula: 'LTLFormula'


class NextFormula(TypedDict):
    """Next: X(formula)"""
    operator: Literal["next"]
    formula: 'LTLFormula'


class MetricEventuallyFormula(TypedDict):
    """Metric Eventually: F_{<=t}(formula)"""
    operator: Literal["metricEventually"]
    timebound: int
    formula: 'LTLFormula'


class MetricAlwaysFormula(TypedDict):
    """Metric Always: G_{<=t}(formula)"""
    operator: Literal["metricAlways"]
    timebound: int
    formula: 'LTLFormula'


class UntilFormula(TypedDict):
    """Temporal until: left U right"""
    operator: Literal["until"]
    left: 'LTLFormula'
    right: 'LTLFormula'


class ReleaseFormula(TypedDict):
    """Temporal release: left R right (dual of until)"""
    operator: Literal["release"]
    left: 'LTLFormula'
    right: 'LTLFormula'


class MetricUntilFormula(TypedDict):
    """Metric Until: left U_{<=t} right"""
    operator: Literal["metricUntil"]
    timebound: int
    left: 'LTLFormula'
    right: 'LTLFormula'


class MetricReleaseFormula(TypedDict):
    """Metric Release: left R_{<=t} right"""
    operator: Literal["metricRelease"]
    timebound: int
    left: 'LTLFormula'
    right: 'LTLFormula'


# Union type for all LTL formulas
LTLFormula = (
    AtomicFormula |
    AndFormula |
    OrFormula |
    NotFormula |
    AlwaysFormula |
    EventuallyFormula |
    NextFormula |
    MetricEventuallyFormula |
    MetricAlwaysFormula |
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
    data: list[int]
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
    signal_name: NotRequired[str]  # Enriched: primary signal name
    actual_value: NotRequired[float | None]  # Enriched: signal value at violation
    condition: NotRequired[str]  # Enriched: e.g. "< 200"


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
