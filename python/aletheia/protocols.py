"""Type definitions for structured data

Defines TypedDict classes, Literal types, and Enums for well-known structures.
This provides better type safety and IDE support.
"""

from enum import Enum
from fractions import Fraction
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
    DUPLICATE_ATTRIBUTE_NAME = "duplicate_attribute_name"
    UNKNOWN_COMMENT_TARGET = "unknown_comment_target"
    UNKNOWN_MESSAGE_SENDER = "unknown_message_sender"


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
    """DBC signal that is always present.

    Numeric fields (factor/offset/minimum/maximum) use ``Fraction`` to
    preserve the Agda core's exact rational representation end-to-end.
    ``receivers`` is the trailing node list from the ``SG_`` line
    (empty list when only the ``Vector__XXX`` placeholder is present).
    """
    name: str
    startBit: int
    length: int
    byteOrder: ByteOrder
    signed: bool
    factor: Fraction
    offset: Fraction
    minimum: Fraction
    maximum: Fraction
    unit: str
    presence: SignalPresence
    receivers: NotRequired[list[str]]


class DBCSignalMultiplexed(TypedDict):
    """DBC signal that is conditionally present (multiplexed).

    Numeric fields (factor/offset/minimum/maximum) use ``Fraction`` to
    preserve the Agda core's exact rational representation end-to-end.
    ``receivers`` is the trailing node list from the ``SG_`` line
    (empty list when only the ``Vector__XXX`` placeholder is present).
    """
    name: str
    startBit: int
    length: int
    byteOrder: ByteOrder
    signed: bool
    factor: Fraction
    offset: Fraction
    minimum: Fraction
    maximum: Fraction
    unit: str
    multiplexor: str
    multiplex_values: list[int]
    receivers: NotRequired[list[str]]


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
    senders: NotRequired[list[str]]  # Additional BO_TX_BU_ transmitters (primary is ``sender``)
    signals: list[DBCSignal]
    extended: NotRequired[bool]  # Optional: true for 29-bit, false/absent for 11-bit


class DBCSignalGroup(TypedDict):
    """DBC signal group (``SIG_GROUP_`` keyword).

    The DBC spec carries a parent-message id and a repetition count on the
    wire; the Agda core only models the flattened ``{name, signals}`` view
    because signal-name uniqueness is enforced globally by the validator,
    so reconstructing message context on format_dbc is unnecessary.
    """
    name: str
    signals: list[str]


# DBC environment variable type (``EV_`` ``type`` field).
# The DBC spec encodes int/float/string as 0/1/2 respectively; the Agda
# core preserves that wire vocabulary directly (``varTypeToℕ``).
DBCVarType = Literal[0, 1, 2]


class DBCEnvironmentVar(TypedDict):
    """DBC environment variable (``EV_`` keyword).

    Numeric fields (initial/minimum/maximum) use ``Fraction`` for the same
    reason as ``DBCSignalAlways`` — the Agda core works in ℚ and exact
    rational precision has to survive the wire round-trip.
    """
    name: str
    varType: DBCVarType
    initial: Fraction
    minimum: Fraction
    maximum: Fraction


class DBCValueEntry(TypedDict):
    """One entry in a DBC value table (numeric value → description)."""
    value: int
    description: str


class DBCValueTable(TypedDict):
    """DBC value table (``VAL_TABLE_`` keyword)."""
    name: str
    entries: list[DBCValueEntry]


# ----------------------------------------------------------------------------
# Tier 2 DBC metadata: nodes / comments / attributes
# ----------------------------------------------------------------------------
# Every tagged wire object (CommentTarget, AttrType, AttrValue, AttrTarget,
# DBCAttribute) uses ``"kind"`` as the first-field discriminator. This mirrors
# the Agda formatter exactly (see ``Formatter.agda`` ``formatCommentTarget`` /
# ``formatAttribute``), so pyright narrows via ``Literal["kind"]``.

class DBCNode(TypedDict):
    """DBC network node (``BU_`` keyword). Only the declared name is modelled;
    per-node attributes and comments live in the sibling arrays."""
    name: str


class DBCCommentTargetNetwork(TypedDict):
    """Network-wide comment (``CM_ "..."``)."""
    kind: Literal["network"]


class DBCCommentTargetNode(TypedDict):
    """Node comment (``CM_ BU_ <name> "..."``)."""
    kind: Literal["node"]
    node: str


class DBCCommentTargetMessage(TypedDict):
    """Message comment (``CM_ BO_ <id> "..."``).

    ``extended`` follows the same convention as ``DBCMessage``: ``true`` for
    29-bit IDs, absent/``false`` for 11-bit IDs.
    """
    kind: Literal["message"]
    id: int
    extended: NotRequired[bool]


class DBCCommentTargetSignal(TypedDict):
    """Signal comment (``CM_ SG_ <id> <signal> "..."``)."""
    kind: Literal["signal"]
    id: int
    extended: NotRequired[bool]
    signal: str


class DBCCommentTargetEnvVar(TypedDict):
    """Environment-variable comment (``CM_ EV_ <name> "..."``)."""
    kind: Literal["envVar"]
    envVar: str


DBCCommentTarget = (
    DBCCommentTargetNetwork |
    DBCCommentTargetNode |
    DBCCommentTargetMessage |
    DBCCommentTargetSignal |
    DBCCommentTargetEnvVar
)


class DBCComment(TypedDict):
    """A DBC ``CM_`` entry with its target and body."""
    target: DBCCommentTarget
    text: str


# Attribute scope matches Agda ``AttrScope``. ``nodeMsg`` / ``nodeSig`` are
# the relational scopes introduced by ``BA_DEF_REL_`` (``BU_BO_REL_`` /
# ``BU_SG_REL_`` in DBC text).
AttrScope = Literal[
    "network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig"
]


class DBCAttrTypeInt(TypedDict):
    """Integer attribute definition (``INT min max``).

    ``min`` / ``max`` are encoded as JSON numbers and carry the full ℤ range
    of the Agda core — handlers that marshal them should use unbounded
    integers, not fixed-width.
    """
    kind: Literal["int"]
    min: int
    max: int


class DBCAttrTypeFloat(TypedDict):
    """Float attribute definition (``FLOAT min max``).

    Bounds are ``Fraction`` to preserve ℚ precision across the wire;
    cantools emits ``float`` literals which the converter widens to
    ``Fraction`` for lossless round-trip.
    """
    kind: Literal["float"]
    min: Fraction
    max: Fraction


class DBCAttrTypeString(TypedDict):
    """String attribute definition (``STRING``)."""
    kind: Literal["string"]


class DBCAttrTypeEnum(TypedDict):
    """Enum attribute definition (``ENUM "a","b",...``)."""
    kind: Literal["enum"]
    values: list[str]


class DBCAttrTypeHex(TypedDict):
    """Hex attribute definition (``HEX min max``). Bounds are unsigned ℕ."""
    kind: Literal["hex"]
    min: int
    max: int


DBCAttrType = (
    DBCAttrTypeInt |
    DBCAttrTypeFloat |
    DBCAttrTypeString |
    DBCAttrTypeEnum |
    DBCAttrTypeHex
)


class DBCAttrValueInt(TypedDict):
    """Integer attribute value (BA_/BA_DEF_DEF_/BA_REL_ for ``INT``)."""
    kind: Literal["int"]
    value: int


class DBCAttrValueFloat(TypedDict):
    """Float attribute value (``FLOAT``). ``Fraction`` mirrors
    ``DBCAttrTypeFloat.min`` / ``max``."""
    kind: Literal["float"]
    value: Fraction


class DBCAttrValueString(TypedDict):
    """String attribute value."""
    kind: Literal["string"]
    value: str


class DBCAttrValueEnum(TypedDict):
    """Enum attribute value: ``value`` is a 0-based index into the matching
    definition's ``values`` list (ℕ on the Agda side), not the label."""
    kind: Literal["enum"]
    value: int


class DBCAttrValueHex(TypedDict):
    """Hex attribute value (unsigned ℕ)."""
    kind: Literal["hex"]
    value: int


DBCAttrValue = (
    DBCAttrValueInt |
    DBCAttrValueFloat |
    DBCAttrValueString |
    DBCAttrValueEnum |
    DBCAttrValueHex
)


class DBCAttrTargetNetwork(TypedDict):
    """Network-scope attribute assignment (``BA_ "attr" value;``)."""
    kind: Literal["network"]


class DBCAttrTargetNode(TypedDict):
    """Node-scope assignment (``BA_ "attr" BU_ <node> value;``)."""
    kind: Literal["node"]
    node: str


class DBCAttrTargetMessage(TypedDict):
    """Message-scope assignment (``BA_ "attr" BO_ <id> value;``)."""
    kind: Literal["message"]
    id: int
    extended: NotRequired[bool]


class DBCAttrTargetSignal(TypedDict):
    """Signal-scope assignment (``BA_ "attr" SG_ <id> <sig> value;``)."""
    kind: Literal["signal"]
    id: int
    extended: NotRequired[bool]
    signal: str


class DBCAttrTargetEnvVar(TypedDict):
    """EnvVar-scope assignment (``BA_ "attr" EV_ <name> value;``)."""
    kind: Literal["envVar"]
    envVar: str


class DBCAttrTargetNodeMsg(TypedDict):
    """Node-message relational assignment (``BA_REL_ ... BU_BO_REL_ ...``)."""
    kind: Literal["nodeMsg"]
    node: str
    id: int
    extended: NotRequired[bool]


class DBCAttrTargetNodeSig(TypedDict):
    """Node-signal relational assignment (``BA_REL_ ... BU_SG_REL_ ...``)."""
    kind: Literal["nodeSig"]
    node: str
    id: int
    extended: NotRequired[bool]
    signal: str


DBCAttrTarget = (
    DBCAttrTargetNetwork |
    DBCAttrTargetNode |
    DBCAttrTargetMessage |
    DBCAttrTargetSignal |
    DBCAttrTargetEnvVar |
    DBCAttrTargetNodeMsg |
    DBCAttrTargetNodeSig
)


class DBCAttrDef(TypedDict):
    """Attribute declaration (``BA_DEF_`` / ``BA_DEF_REL_``)."""
    kind: Literal["definition"]
    name: str
    scope: AttrScope
    attrType: DBCAttrType


class DBCAttrDefault(TypedDict):
    """Attribute default (``BA_DEF_DEF_`` / ``BA_DEF_DEF_REL_``)."""
    kind: Literal["default"]
    name: str
    value: DBCAttrValue


class DBCAttrAssign(TypedDict):
    """Attribute assignment (``BA_`` / ``BA_REL_``)."""
    kind: Literal["assignment"]
    name: str
    target: DBCAttrTarget
    value: DBCAttrValue


# The three BA_* sub-records live in a single flat list so wire ordering
# (definition → default → assignment) is preserved end-to-end; the ``kind``
# discriminator lets the Agda parser dispatch without separate arrays.
DBCAttribute = DBCAttrDef | DBCAttrDefault | DBCAttrAssign


class DBCDefinition(TypedDict):
    """Complete DBC file structure.

    Every metadata array is ``NotRequired`` so that pre-Tier-1/2 wire
    payloads and hand-written fixtures remain accepted; absent keys are
    treated as empty lists by both ``dbc_to_json`` consumers and the Agda
    parser.
    """
    version: str
    messages: list[DBCMessage]
    signalGroups: NotRequired[list[DBCSignalGroup]]
    environmentVars: NotRequired[list[DBCEnvironmentVar]]
    valueTables: NotRequired[list[DBCValueTable]]
    nodes: NotRequired[list[DBCNode]]
    comments: NotRequired[list[DBCComment]]
    attributes: NotRequired[list[DBCAttribute]]


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
    """Next: X(formula).

    Discouraged in CAN analysis — prefer ``within(time_ms)`` /
    ``metric_until``. CAN timing jitter makes frame-exact semantics
    unreliable; kept for standard-LTLf completeness.
    """
    operator: Literal["next"]
    formula: 'LTLFormula'


class WeakNextFormula(TypedDict):
    """Weak Next: WX(formula) — holds vacuously at end of stream.

    Discouraged in CAN analysis — prefer ``within(time_ms)`` /
    ``metric_until``. CAN timing jitter makes frame-exact semantics
    unreliable; kept for standard-LTLf completeness.
    """
    operator: Literal["weakNext"]
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
    WeakNextFormula |
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
    """Signal name-value pair from signal extraction (output from Agda).

    ``value`` is a ``Fraction`` to preserve the Agda core's exact rational
    representation — extraction responses encode non-integer values as
    ``{"numerator": n, "denominator": d}`` on the wire.
    """
    name: str
    value: Fraction


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


class ParseDBCTextCommand(TypedDict):
    """Parse DBC from raw DBC text using the verified Agda text parser"""
    type: Literal["command"]
    command: Literal["parseDBCText"]
    text: str


# Union type for JSON-path commands (binary FFI operations are not represented here).
Command = ParseDBCCommand | SetPropertiesCommand | ValidateDBCCommand | ParseDBCTextCommand


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


class ViolationEnrichment(TypedDict):
    """Human-readable context attached to property violations.

    Mirrors Go's ``ViolationEnrichment`` and C++'s ``ViolationEnrichment``
    structs. ``enriched_reason`` is computed by the Python enrichment layer
    from signal values and formula structure; ``core_reason`` is the raw
    reason from the Agda core (may be empty).
    """
    signals: dict[str, Fraction | None]
    formula_desc: str
    enriched_reason: str
    core_reason: str


class PropertyViolationResponse(TypedDict):
    """Property violation response"""
    status: Literal["fails"]
    type: Literal["property"]
    property_index: RationalNumber
    timestamp: RationalNumber
    reason: NotRequired[str]  # Optional reason field from binary
    enrichment: NotRequired[ViolationEnrichment]  # Auto-derived diagnostic


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
    enrichment: NotRequired[ViolationEnrichment]  # Auto-derived diagnostic


class CompleteResponse(TypedDict):
    """Stream complete response with per-property finalization results"""
    status: Literal["complete"]
    results: list[PropertyResultEntry]


class ExtractSignalsResponse(TypedDict):
    """Response from extractAllSignals command"""
    status: Literal["success"]
    values: list[SignalValue]
    errors: list[SignalError]
    absent: list[str]


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


class ParsedDBCResponse(TypedDict):
    """Response from parseDBC and parseDBCText commands.

    Carries the parsed body (canonical Agda-side ``DBCDefinition``) plus any
    non-error validation issues (warnings).  Errors short-circuit to
    ``ErrorResponse``; this shape is only emitted when the parsed DBC passes
    every error-severity check.
    """
    status: Literal["success"]
    dbc: DBCDefinition
    warnings: list[ValidationIssue]


# Union type for all responses
Response = (
    SuccessResponse |
    ErrorResponse |
    AckResponse |
    PropertyViolationResponse |
    CompleteResponse |
    ExtractSignalsResponse |
    FormatDBCResponse |
    ValidationResponse |
    ParsedDBCResponse
)


# Explicit public surface — mirrors the imports in ``_client.py``, ``cli.py``,
# and the top-level ``aletheia/__init__.py`` facade.  Keeping this list
# explicit (rather than relying on ``*`` re-export) means a private helper
# added below does not accidentally leak into the binding API surface, and
# consumers get a stable grep target for the cross-binding protocol vocabulary.
__all__ = [
    # Type guards
    "is_str_dict",
    "is_object_list",
    # Literals
    "ByteOrder",
    "SignalPresence",
    # Enums
    "IssueSeverity",
    "IssueCode",
    "PredicateType",
    # DBC types
    "DBCSignal",
    "DBCSignalAlways",
    "DBCSignalMultiplexed",
    "DBCMessage",
    "DBCDefinition",
    "DBCSignalGroup",
    "DBCVarType",
    "DBCEnvironmentVar",
    "DBCValueEntry",
    "DBCValueTable",
    # Tier 2 DBC metadata
    "DBCNode",
    "DBCComment",
    "DBCCommentTarget",
    "DBCCommentTargetNetwork",
    "DBCCommentTargetNode",
    "DBCCommentTargetMessage",
    "DBCCommentTargetSignal",
    "DBCCommentTargetEnvVar",
    "AttrScope",
    "DBCAttrType",
    "DBCAttrTypeInt",
    "DBCAttrTypeFloat",
    "DBCAttrTypeString",
    "DBCAttrTypeEnum",
    "DBCAttrTypeHex",
    "DBCAttrValue",
    "DBCAttrValueInt",
    "DBCAttrValueFloat",
    "DBCAttrValueString",
    "DBCAttrValueEnum",
    "DBCAttrValueHex",
    "DBCAttrTarget",
    "DBCAttrTargetNetwork",
    "DBCAttrTargetNode",
    "DBCAttrTargetMessage",
    "DBCAttrTargetSignal",
    "DBCAttrTargetEnvVar",
    "DBCAttrTargetNodeMsg",
    "DBCAttrTargetNodeSig",
    "DBCAttribute",
    "DBCAttrDef",
    "DBCAttrDefault",
    "DBCAttrAssign",
    # Signal predicates
    "SignalPredicate",
    "EqualsPredicate",
    "LessThanPredicate",
    "GreaterThanPredicate",
    "LessThanOrEqualPredicate",
    "GreaterThanOrEqualPredicate",
    "BetweenPredicate",
    "ChangedByPredicate",
    "StableWithinPredicate",
    # LTL formulas
    "LTLFormula",
    "AtomicFormula",
    "AndFormula",
    "OrFormula",
    "NotFormula",
    "AlwaysFormula",
    "EventuallyFormula",
    "NextFormula",
    "WeakNextFormula",
    "MetricEventuallyFormula",
    "MetricAlwaysFormula",
    "UntilFormula",
    "ReleaseFormula",
    "MetricUntilFormula",
    "MetricReleaseFormula",
    # Rational / signal values
    "RationalNumber",
    "SignalValue",
    "SignalError",
    # Commands
    "Command",
    "ParseDBCCommand",
    "SetPropertiesCommand",
    "ValidateDBCCommand",
    "ParseDBCTextCommand",
    # Responses
    "Response",
    "SuccessResponse",
    "ErrorResponse",
    "AckResponse",
    "ViolationEnrichment",
    "PropertyViolationResponse",
    "PropertyResultEntry",
    "CompleteResponse",
    "ExtractSignalsResponse",
    "FormatDBCResponse",
    "ValidationIssue",
    "ValidationResponse",
    "ParsedDBCResponse",
]
