"""Type definitions for structured data

Defines TypedDict classes, Literal types, and Enums for well-known structures.
This provides better type safety and IDE support.
"""

from __future__ import annotations

from enum import Enum
from typing import TypedDict, TypeGuard, NotRequired, Literal, cast


def is_str_dict(val: object) -> TypeGuard[dict[str, object]]:
    """Narrow ``object`` to ``dict[str, object]``."""
    return isinstance(val, dict) and all(
        isinstance(k, str) for k in cast(dict[object, object], val)
    )


def is_object_list(val: object) -> TypeGuard[list[object]]:
    """Narrow ``object`` to ``list[object]``, avoiding ``list[Unknown]``."""
    return isinstance(val, list)


ByteOrder = Literal["little_endian", "big_endian"]

SignalPresence = Literal["always"]


class IssueSeverity(str, Enum):
    """Validation issue severity"""
    ERROR = "error"
    WARNING = "warning"


class IssueCode(str, Enum):
    """Validation issue codes matching Agda IssueCode enum"""
    DUPLICATE_MESSAGE_ID = "duplicate_message_id"
    DUPLICATE_SIGNAL_NAME = "duplicate_signal_name"
    FACTOR_ZERO = "factor_zero"
    MULTIPLEXOR_NOT_FOUND = "multiplexor_not_found"
    MULTIPLEXOR_CYCLE = "multiplexor_cycle"
    GLOBAL_NAME_COLLISION = "global_name_collision"
    MIN_EXCEEDS_MAX = "min_exceeds_max"
    SIGNAL_EXCEEDS_DLC = "signal_exceeds_dlc"
    SIGNAL_OVERLAP = "signal_overlap"
    BIT_LENGTH_ZERO = "bit_length_zero"
    DUPLICATE_MESSAGE_NAME = "duplicate_message_name"
    OFFSET_SCALE_RANGE = "offset_scale_range"
    EMPTY_MESSAGE = "empty_message"
    START_BIT_OUT_OF_RANGE = "start_bit_out_of_range"
    BIT_LENGTH_EXCESSIVE = "bit_length_excessive"
    MULTIPLEXOR_NON_UNIT_SCALING = "multiplexor_non_unit_scaling"


class ErrorCode(str, Enum):
    """Machine-readable error codes matching Agda Error ADT.

    Each code maps 1:1 to an Agda error constructor via errorCode.
    """
    # Parse errors
    PARSE_MISSING_FIELD = "parse_missing_field"
    PARSE_INVALID_BYTE_ORDER = "parse_invalid_byte_order"
    PARSE_INVALID_PRESENCE = "parse_invalid_presence"
    PARSE_MISSING_SIGNED = "parse_missing_signed"
    PARSE_INVALID_SIGNED = "parse_invalid_signed"
    PARSE_NOT_AN_OBJECT = "parse_not_an_object"
    PARSE_EXT_CAN_ID_OUT_OF_RANGE = "parse_ext_can_id_out_of_range"
    PARSE_STD_CAN_ID_OUT_OF_RANGE = "parse_std_can_id_out_of_range"
    PARSE_DEFAULT_CAN_ID_OUT_OF_RANGE = "parse_default_can_id_out_of_range"
    PARSE_INVALID_DLC_BYTES = "parse_invalid_dlc_bytes"
    PARSE_ROOT_NOT_OBJECT = "parse_root_not_object"
    PARSE_MISSING_SIGNAL_NAME = "parse_missing_signal_name"
    PARSE_SIGNAL_BIT_LENGTH_ZERO = "parse_signal_bit_length_zero"
    PARSE_SIGNAL_OVERFLOWS_FRAME = "parse_signal_overflows_frame"
    PARSE_SIGNAL_MSB_BELOW_BIT_LENGTH = "parse_signal_msb_below_bit_length"
    # Frame errors
    FRAME_SIGNAL_NOT_FOUND = "frame_signal_not_found"
    FRAME_SIGNAL_INDEX_OOB = "frame_signal_index_oob"
    FRAME_INJECTION_FAILED = "frame_injection_failed"
    FRAME_SIGNALS_OVERLAP = "frame_signals_overlap"
    FRAME_CAN_ID_NOT_FOUND = "frame_can_id_not_found"
    FRAME_CAN_ID_MISMATCH = "frame_can_id_mismatch"
    # Route errors
    ROUTE_MISSING_FIELD = "route_missing_field"
    ROUTE_MISSING_ARRAY = "route_missing_array"
    ROUTE_UNKNOWN_COMMAND = "route_unknown_command"
    ROUTE_MISSING_COMMAND_FIELD = "route_missing_command_field"
    ROUTE_DLC_EXCEEDS_MAX = "route_dlc_exceeds_max"
    ROUTE_BYTE_ARRAY_PARSE_FAILED = "route_byte_array_parse_failed"
    ROUTE_BYTE_COUNT_MISMATCH = "route_byte_count_mismatch"
    ROUTE_MISSING_DBC_FIELD = "route_missing_dbc_field"
    ROUTE_MISSING_PROPS_FIELD = "route_missing_props_field"
    # Handler errors
    HANDLER_NO_DBC = "handler_no_dbc"
    HANDLER_ALREADY_STREAMING = "handler_already_streaming"
    HANDLER_NOT_STREAMING = "handler_not_streaming"
    HANDLER_STREAM_NOT_STARTED = "handler_stream_not_started"
    HANDLER_STREAM_ACTIVE = "handler_stream_active"
    HANDLER_SIGNAL_LIST_PARSE_FAILED = "handler_signal_list_parse_failed"
    HANDLER_PROPERTY_PARSE_FAILED = "handler_property_parse_failed"
    HANDLER_INVALID_DLC_CODE = "handler_invalid_dlc_code"
    HANDLER_VALIDATION_FAILED = "handler_validation_failed"
    HANDLER_NON_MONOTONIC_TIMESTAMP = "handler_non_monotonic_timestamp"
    # Dispatch errors
    DISPATCH_MISSING_TYPE_FIELD = "dispatch_missing_type_field"
    DISPATCH_UNKNOWN_MESSAGE_TYPE = "dispatch_unknown_message_type"
    DISPATCH_INVALID_JSON = "dispatch_invalid_json"
    DISPATCH_REQUEST_NOT_OBJECT = "dispatch_request_not_object"


class PredicateType(str, Enum):
    """Signal predicate types matching Agda JSON schema"""
    EQUALS = "equals"
    LESS_THAN = "lessThan"
    GREATER_THAN = "greaterThan"
    LESS_THAN_OR_EQUAL = "lessThanOrEqual"
    GREATER_THAN_OR_EQUAL = "greaterThanOrEqual"
    BETWEEN = "between"
    CHANGED_BY = "changedBy"
    STABLE_WITHIN = "stableWithin"


# ============================================================================
# DBC Structure Types
# ============================================================================

class DBCSignalAlways(TypedDict):
    """DBC signal that is always present"""
    name: str
    startBit: int
    length: int
    byteOrder: ByteOrder
    signed: bool
    factor: float
    offset: float
    minimum: float
    maximum: float
    unit: str
    presence: SignalPresence


class DBCSignalMultiplexed(TypedDict):
    """DBC signal that is conditionally present (multiplexed)"""
    name: str
    startBit: int
    length: int
    byteOrder: ByteOrder
    signed: bool
    factor: float
    offset: float
    minimum: float
    maximum: float
    unit: str
    multiplexor: str
    multiplex_values: list[int]


# Union type for all signal types
DBCSignal = DBCSignalAlways | DBCSignalMultiplexed


class DBCMessage(TypedDict):
    """DBC message definition structure.

    Note: ``dlc`` is the payload byte count (from ``cantools message.length``),
    not the raw DLC code.  For CAN 2.0B (DLC 0-8) the values coincide;
    for CAN-FD (DLC 9-15) this field holds 12/16/20/24/32/48/64.
    The JSON key name ``"dlc"`` matches the Agda parser's wire format.
    """
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
    """ChangedBy predicate: directional change detection.

    Positive delta: curr - prev >= delta (increased by at least delta)
    Negative delta: curr - prev <= delta (decreased by at least |delta|)
    """
    predicate: Literal["changedBy"]
    signal: str
    delta: float


class StableWithinPredicate(TypedDict):
    """StableWithin predicate: |signal_now - signal_prev| <= tolerance"""
    predicate: Literal["stableWithin"]
    signal: str
    tolerance: float


SignalPredicate = (
    EqualsPredicate |
    LessThanPredicate |
    GreaterThanPredicate |
    LessThanOrEqualPredicate |
    GreaterThanOrEqualPredicate |
    BetweenPredicate |
    ChangedByPredicate |
    StableWithinPredicate
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


class ValidateDBCCommand(TypedDict):
    """Validate a parsed DBC definition"""
    type: Literal["command"]
    command: Literal["validateDBC"]
    dbc: DBCDefinition


# Union type for JSON-path commands (binary FFI operations are not represented here).
Command = ParseDBCCommand | SetPropertiesCommand | ValidateDBCCommand


class SuccessResponse(TypedDict):
    """Success response"""
    status: Literal["success"]
    message: NotRequired[str]


class ErrorResponse(TypedDict):
    """Error response with machine-readable code"""
    status: Literal["error"]
    code: str
    message: str


class AckResponse(TypedDict):
    """Acknowledgment response"""
    status: Literal["ack"]


class PropertyViolationResponse(TypedDict):
    """Property violation response"""
    status: Literal["fails"]
    type: Literal["property"]
    property_index: RationalNumber
    timestamp: RationalNumber
    reason: NotRequired[str]  # Optional reason field from binary
    signals: NotRequired[dict[str, float | None]]  # Enriched: signal values
    formula: NotRequired[str]  # Enriched: human-readable formula
    enriched_reason: NotRequired[str]  # Enriched: counter-example string


class PropertyResultEntry(TypedDict):
    """A single property finalization result at end-of-stream.

    ``status="unresolved"`` means the Agda coalgebra's three-valued Kleene
    ``finalizeL`` returned ``Unsure`` — typically when an atomic predicate's
    signal was never observed on the trace, so neither satisfaction nor
    violation can be proved. The denotational semantics agrees this is
    Unknown, so it is reported as a distinct verdict rather than collapsed
    to a failure.
    """
    type: Literal["property"]
    status: Literal["fails", "holds", "unresolved"]
    property_index: RationalNumber
    timestamp: NotRequired[RationalNumber]  # Only for violations
    reason: NotRequired[str]  # Only for violations and unresolved
    signals: NotRequired[dict[str, float | None]]  # Enriched: signal values
    formula: NotRequired[str]  # Enriched: human-readable formula
    enriched_reason: NotRequired[str]  # Enriched: counter-example string


class CompleteResponse(TypedDict):
    """Stream complete response with per-property finalization results"""
    status: Literal["complete"]
    results: list[PropertyResultEntry]


class BuildFrameResponse(TypedDict):
    """Response from buildFrame command"""
    status: Literal["success"]
    data: list[int]


class ExtractSignalsResponse(TypedDict):
    """Response from extractAllSignals command"""
    status: Literal["success"]
    values: list[SignalValue]
    errors: list[SignalError]
    absent: list[str]


class UpdateFrameResponse(TypedDict):
    """Response from updateFrame command"""
    status: Literal["success"]
    data: list[int]


class FormatDBCResponse(TypedDict):
    """Response from formatDBC command"""
    status: Literal["success"]
    dbc: DBCDefinition


class ValidationIssue(TypedDict):
    """A single DBC validation issue"""
    severity: IssueSeverity
    code: IssueCode
    detail: str


class ValidationResponse(TypedDict):
    """Response from validateDBC command"""
    status: Literal["validation"]
    has_errors: bool
    issues: list[ValidationIssue]


# Union type for all responses
Response = (
    SuccessResponse |
    ErrorResponse |
    AckResponse |
    PropertyViolationResponse |
    CompleteResponse |
    BuildFrameResponse |
    ExtractSignalsResponse |
    UpdateFrameResponse |
    FormatDBCResponse |
    ValidationResponse
)
