# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Type definitions for structured data.

Defines TypedDict classes, Literal types, and Enums for well-known structures.
This provides better type safety and IDE support.

The DBC sub-schema lives in :mod:`aletheia._dbc_types`; this module
re-exports its public names so consumers can keep importing from
``aletheia.protocols`` directly.
"""

import json
from enum import StrEnum
from fractions import Fraction
from typing import TYPE_CHECKING, Literal, NotRequired, TypedDict, TypeGuard, cast

from aletheia._dbc_types import (
    AttrScope,
    ByteOrder,
    DBCAttrAssign,
    DBCAttrDef,
    DBCAttrDefault,
    DBCAttribute,
    DBCAttrTarget,
    DBCAttrTargetEnvVar,
    DBCAttrTargetMessage,
    DBCAttrTargetNetwork,
    DBCAttrTargetNode,
    DBCAttrTargetNodeMsg,
    DBCAttrTargetNodeSig,
    DBCAttrTargetSignal,
    DBCAttrType,
    DBCAttrTypeEnum,
    DBCAttrTypeFloat,
    DBCAttrTypeHex,
    DBCAttrTypeInt,
    DBCAttrTypeString,
    DBCAttrValue,
    DBCAttrValueEnum,
    DBCAttrValueFloat,
    DBCAttrValueHex,
    DBCAttrValueInt,
    DBCAttrValueString,
    DBCComment,
    DBCCommentTarget,
    DBCCommentTargetEnvVar,
    DBCCommentTargetMessage,
    DBCCommentTargetNetwork,
    DBCCommentTargetNode,
    DBCCommentTargetSignal,
    DBCDefinition,
    DBCEnvironmentVar,
    DBCMessage,
    DBCNode,
    DBCRawValueDesc,
    DBCSignal,
    DBCSignalAlways,
    DBCSignalGroup,
    DBCSignalMultiplexed,
    DBCValueEntry,
    DBCValueTable,
    DBCVarType,
    DLCByteCount,
    DLCCode,
    SignalPresence,
)

if TYPE_CHECKING:
    from aletheia.issue_codes import ValidationIssue

# ─── Public wire helpers ───────────────────────────────────────────────────
# Promoted from ``client/_helpers.py`` so non-client modules
# (``cli.py``, ``dbc_converter.py``, ``excel_loader.py``) can reach a
# public surface rather than ``aletheia.client._helpers`` (a private
# implementation module).  ``client/_helpers.py`` re-imports these names
# for backward-compat with client-internal callers.


class FractionJSONEncoder(json.JSONEncoder):
    """JSON encoder that handles :class:`fractions.Fraction` losslessly.

    Emits an integer when the denominator is 1, and a
    ``{"numerator": N, "denominator": D}`` dict otherwise.  This is the
    wire shape Agda's :func:`Aletheia.DBC.Types.rationalToJSON` accepts
    and the C++/Go bindings emit; pinning it client-side gives byte-
    identical JSON across the three bindings.
    """

    def default(self, o: object) -> object:
        if isinstance(o, Fraction):
            if o.denominator == 1:
                return o.numerator
            return {"numerator": o.numerator, "denominator": o.denominator}
        return super().default(o)


def dump_json(value: object, *, indent: int | None = None) -> str:
    r"""Serialize *value* to JSON, handling Fraction via FractionJSONEncoder.

    ``ensure_ascii=False`` is pinned so identifier and string-literal
    fields with non-ASCII characters (DBC permits non-ASCII in
    ``CM_`` text bodies, comments, and similar opaque-tail consumers)
    serialize as their UTF-8 bytes rather than ``\uXXXX`` escapes.  The
    Agda-side parser is byte-oriented; the Go and C++ bindings emit
    UTF-8 directly — pinning ``ensure_ascii=False`` keeps Python
    byte-identical with them (cross-binding wire-byte parity).
    """
    return json.dumps(value, cls=FractionJSONEncoder, indent=indent, ensure_ascii=False)


def to_signal_fraction(value: float | Fraction) -> Fraction:
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
    return Fraction(value).limit_denominator(_DECIMAL_PRECISION_DEN_PROTOCOLS)


_DECIMAL_PRECISION_DEN_PROTOCOLS = 1_000_000_000  # mirrors client/_helpers.py


def is_str_dict(val: object) -> TypeGuard[dict[str, object]]:
    """Narrow ``object`` to ``dict[str, object]``.

    Returns:
        ``True`` when *val* is a ``dict`` and every key is a ``str`` —
        the precondition for safe ``dict.get(key)`` calls under
        ``object`` keys.  The check is one ``isinstance`` plus a key
        scan; not free for large dicts but the values are O(1) to
        access afterwards under the narrowed type.

    """
    return isinstance(val, dict) and all(
        isinstance(k, str) for k in cast("dict[object, object]", val)
    )


def is_object_list(val: object) -> TypeGuard[list[object]]:
    """Narrow ``object`` to ``list[object]``, avoiding ``list[Unknown]``.

    Returns:
        ``True`` when *val* is a ``list``.  Element types remain
        ``object``; the caller is responsible for per-element narrowing
        before accessing them.  Used to dispatch on "is this a JSON
        array" before iterating.

    """
    return isinstance(val, list)


class PredicateType(StrEnum):
    """Signal predicate types matching Agda JSON schema."""

    EQUALS = "equals"
    LESS_THAN = "lessThan"
    GREATER_THAN = "greaterThan"
    LESS_THAN_OR_EQUAL = "lessThanOrEqual"
    GREATER_THAN_OR_EQUAL = "greaterThanOrEqual"
    BETWEEN = "between"
    CHANGED_BY = "changedBy"
    STABLE_WITHIN = "stableWithin"


# ============================================================================
# LTL Formula Types - Agda-compatible JSON schema
# ============================================================================
# All formulas use "operator" key (not "type").
# Predicates use {"operator": "atomic", "predicate": {...}} format.
# Time bounds use "timebound" key (not "time_ms").
# "never" and "implies" are desugared by Python before sending to Agda.

# -- Signal Predicates (inside "predicate" object) --
#
# Per the DecRat universal principle, every numeric value crossing the
# wire from a predicate carries an exact :class:`Fraction` — the Agda
# kernel's parser accepts bare integer literals, decimal floats, AND
# rational dicts (``{"numerator": n, "denominator": d}``); the
# :class:`FractionJSONEncoder` emits the latter shape via the
# canonical numerator/denominator pair so cross-binding wire bytes match
# C++'s ``rational_to_json``.


class EqualsPredicate(TypedDict):
    """Equals predicate: signal == value."""

    predicate: Literal["equals"]
    signal: str
    value: Fraction


class LessThanPredicate(TypedDict):
    """LessThan predicate: signal < value."""

    predicate: Literal["lessThan"]
    signal: str
    value: Fraction


class GreaterThanPredicate(TypedDict):
    """GreaterThan predicate: signal > value."""

    predicate: Literal["greaterThan"]
    signal: str
    value: Fraction


class LessThanOrEqualPredicate(TypedDict):
    """LessThanOrEqual predicate: signal <= value."""

    predicate: Literal["lessThanOrEqual"]
    signal: str
    value: Fraction


class GreaterThanOrEqualPredicate(TypedDict):
    """GreaterThanOrEqual predicate: signal >= value."""

    predicate: Literal["greaterThanOrEqual"]
    signal: str
    value: Fraction


class BetweenPredicate(TypedDict):
    """Between predicate: min <= signal <= max."""

    predicate: Literal["between"]
    signal: str
    min: Fraction
    max: Fraction


class ChangedByPredicate(TypedDict):
    """ChangedBy predicate: directional change detection.

    Positive delta: curr - prev >= delta (increased by at least delta)
    Negative delta: curr - prev <= delta (decreased by at least |delta|)
    """

    predicate: Literal["changedBy"]
    signal: str
    delta: Fraction


class StableWithinPredicate(TypedDict):
    """StableWithin predicate: |signal_now - signal_prev| <= tolerance."""

    predicate: Literal["stableWithin"]
    signal: str
    tolerance: Fraction


# A signal predicate is either a comparison (the five relational forms) or a
# range/temporal form.  Naming the comparison subset lets callers that handle
# only comparisons (e.g. the enrichment TypeGuard) reuse it instead of
# restating the arms, and makes the subset relationship explicit.
ComparisonPredicate = (
    EqualsPredicate
    | LessThanPredicate
    | GreaterThanPredicate
    | LessThanOrEqualPredicate
    | GreaterThanOrEqualPredicate
)
SignalPredicate = (
    ComparisonPredicate | BetweenPredicate | ChangedByPredicate | StableWithinPredicate
)


# -- LTL Formula Types (using "operator" key) --


class AtomicFormula(TypedDict):
    """Atomic formula wrapping a signal predicate."""

    operator: Literal["atomic"]
    predicate: SignalPredicate


class AndFormula(TypedDict):
    """Logical AND: left && right."""

    operator: Literal["and"]
    left: LTLFormula
    right: LTLFormula


class OrFormula(TypedDict):
    """Logical OR: left || right."""

    operator: Literal["or"]
    left: LTLFormula
    right: LTLFormula


class NotFormula(TypedDict):
    """Logical NOT: !formula."""

    operator: Literal["not"]
    formula: LTLFormula


class AlwaysFormula(TypedDict):
    """Always (globally): G(formula)."""

    operator: Literal["always"]
    formula: LTLFormula


class EventuallyFormula(TypedDict):
    """Eventually (finally): F(formula)."""

    operator: Literal["eventually"]
    formula: LTLFormula


class NextFormula(TypedDict):
    """Next: X(formula).

    Discouraged in CAN analysis — prefer ``within(time_ms)`` /
    ``metric_until``. CAN timing jitter makes frame-exact semantics
    unreliable; kept for standard-LTLf completeness.
    """

    operator: Literal["next"]
    formula: LTLFormula


class WeakNextFormula(TypedDict):
    """Weak Next: WX(formula) — holds vacuously at end of stream.

    Discouraged in CAN analysis — prefer ``within(time_ms)`` /
    ``metric_until``. CAN timing jitter makes frame-exact semantics
    unreliable; kept for standard-LTLf completeness.
    """

    operator: Literal["weakNext"]
    formula: LTLFormula


class MetricEventuallyFormula(TypedDict):
    """Metric Eventually: F_{<=t}(formula)."""

    operator: Literal["metricEventually"]
    timebound: int
    formula: LTLFormula


class MetricAlwaysFormula(TypedDict):
    """Metric Always: G_{<=t}(formula)."""

    operator: Literal["metricAlways"]
    timebound: int
    formula: LTLFormula


class UntilFormula(TypedDict):
    """Temporal until: left U right."""

    operator: Literal["until"]
    left: LTLFormula
    right: LTLFormula


class ReleaseFormula(TypedDict):
    """Temporal release: left R right (dual of until)."""

    operator: Literal["release"]
    left: LTLFormula
    right: LTLFormula


class MetricUntilFormula(TypedDict):
    """Metric Until: left U_{<=t} right."""

    operator: Literal["metricUntil"]
    timebound: int
    left: LTLFormula
    right: LTLFormula


class MetricReleaseFormula(TypedDict):
    """Metric Release: left R_{<=t} right."""

    operator: Literal["metricRelease"]
    timebound: int
    left: LTLFormula
    right: LTLFormula


# Union type for all LTL formulas
LTLFormula = (
    AtomicFormula
    | AndFormula
    | OrFormula
    | NotFormula
    | AlwaysFormula
    | EventuallyFormula
    | NextFormula
    | WeakNextFormula
    | MetricEventuallyFormula
    | MetricAlwaysFormula
    | UntilFormula
    | ReleaseFormula
    | MetricUntilFormula
    | MetricReleaseFormula
)


# ============================================================================
# Signal Operation Types
# ============================================================================


class RationalNumber(TypedDict):
    """Rational number representation from Agda."""

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
    """Signal name-error pair for extraction failures.

    Emitted when the Agda core cannot compute a signal value on a given
    frame (DLC mismatch, bit range outside payload, unknown signal name
    against the current DBC).  ``error`` is the human-readable reason
    string from the core; pair with :class:`SignalValue` in extraction
    responses, where successful and failed signals share one envelope.
    """

    name: str
    error: str


# ============================================================================
# Command and Response Types
# ============================================================================


class ParseDBCCommand(TypedDict):
    """Parse DBC file command."""

    type: Literal["command"]
    command: Literal["parseDBC"]
    dbc: DBCDefinition


class SetPropertiesCommand(TypedDict):
    """Set LTL properties command."""

    type: Literal["command"]
    command: Literal["setProperties"]
    properties: list[LTLFormula]


class ValidateDBCCommand(TypedDict):
    """Validate a parsed DBC definition."""

    type: Literal["command"]
    command: Literal["validateDBC"]
    dbc: DBCDefinition


class ParseDBCTextCommand(TypedDict):
    """Parse DBC from raw DBC text using the verified Agda text parser."""

    type: Literal["command"]
    command: Literal["parseDBCText"]
    text: str


class FormatDBCTextCommand(TypedDict):
    """Format DBC JSON dict back to .dbc text using the verified Agda formatter.

    The inverse of ``ParseDBCTextCommand`` at the wire level: text → JSON → text
    closes byte-identical for any well-formed DBC (post-Phase-E.9a).
    """

    type: Literal["command"]
    command: Literal["formatDBCText"]
    dbc: DBCDefinition


# Union type for JSON-path commands (binary FFI operations are not represented here).
Command = (
    ParseDBCCommand
    | SetPropertiesCommand
    | ValidateDBCCommand
    | ParseDBCTextCommand
    | FormatDBCTextCommand
)


class SuccessResponse(TypedDict):
    """Success response."""

    status: Literal["success"]
    message: NotRequired[str]


class ErrorResponse(TypedDict):
    """Error response with machine-readable code.

    The ``bound_kind`` / ``observed`` / ``limit`` triple is present on
    InputBoundExceeded errors (``code == "input_bound_exceeded"``;
    previously the three per-ADT codes ``parse_*`` / ``frame_*`` /
    ``dbc_text_*``) and absent on all other error codes; the Agda kernel
    emits the typed payload via ``Protocol/ResponseFormat.errorExtras``.
    """

    status: Literal["error"]
    code: str
    message: str
    bound_kind: NotRequired[str]
    observed: NotRequired[int]
    limit: NotRequired[int]


class AckResponse(TypedDict):
    """Acknowledgment response."""

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


class PropertyBatchResponse(TypedDict):
    """Per-frame batch of property events emitted during streaming.

    Replaces the prior ``PropertyViolationResponse``.  Each
    ``send_frame`` call may now return zero events (``AckResponse``)
    or one-or-more events in this batch.  Inner ``results`` carries each
    event in source-order: any satisfactions that completed before a
    halting violation come first, then the violation itself.  A
    completion-only frame (one or more properties became Satisfied,
    none violated) returns a batch of pure satisfactions.

    Inner element schema matches ``PropertyResultEntry`` (fails / holds /
    unresolved); ``status: "fails"`` carries the violation diagnostics
    (``timestamp``, ``reason``, optional ``enrichment``); ``status: "holds"``
    carries only the ``property_index``.
    """

    type: Literal["property_batch"]
    results: list[PropertyResultEntry]


class PropertyResultEntry(TypedDict):
    """A single property finalization result at end-of-stream.

    ``status="unresolved"`` means the Agda coalgebra's three-valued Kleene
    ``finalizeL`` returned ``Unsure`` — typically when an atomic predicate's
    signal was never observed on the trace, so neither satisfaction nor
    violation can be proved. This is the user-observable manifestation of
    a violated ``AllObserved`` invariant (see
    :class:`AletheiaClient` docstring § "Streaming adequacy"). The
    denotational semantics agrees this is Unknown, so it is reported as a
    distinct verdict rather than collapsed to a failure.
    """

    type: Literal["property"]
    status: Literal["fails", "holds", "unresolved"]
    property_index: RationalNumber
    timestamp: NotRequired[RationalNumber]  # Only for violations
    reason: NotRequired[str]  # Only for violations and unresolved
    enrichment: NotRequired[ViolationEnrichment]  # Auto-derived diagnostic


class CompleteWarning(TypedDict):
    """One EndStream warning surfaced by the kernel.

    Emitted by the Agda walker when a property's atom references a
    signal that never appeared in trace.
    ``kind == "uncached_atom"`` is the only kind today; new kinds are
    additive on the wire (future kinds appear here and the binding
    surfaces them under a string-typed ``kind`` field).
    """

    kind: str
    property_index: int
    detail: str


class CompleteResponse(TypedDict):
    """Stream complete response with per-property finalization results."""

    status: Literal["complete"]
    results: list[PropertyResultEntry]
    warnings: list[CompleteWarning]


class ExtractSignalsResponse(TypedDict):
    """Response from extractAllSignals command."""

    status: Literal["success"]
    values: list[SignalValue]
    errors: list[SignalError]
    absent: list[str]


class FormatDBCResponse(TypedDict):
    """Response from formatDBC command."""

    status: Literal["success"]
    dbc: DBCDefinition


class ValidationResponse(TypedDict):
    """Response from validateDBC command."""

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


class DBCTextResponse(TypedDict):
    """Response from formatDBCText command (Track E.10).

    Carries the .dbc text image produced by ``formatText`` over a JSON DBC
    input.  Errors (JSON parse failure on the input) short-circuit to
    ``ErrorResponse``.
    """

    status: Literal["success"]
    text: str


# Union type for all responses
Response = (
    SuccessResponse
    | ErrorResponse
    | AckResponse
    | PropertyBatchResponse
    | CompleteResponse
    | ExtractSignalsResponse
    | FormatDBCResponse
    | ValidationResponse
    | ParsedDBCResponse
    | DBCTextResponse
)


# Explicit public surface — mirrors the imports in ``_client.py``, ``cli.py``,
# and the top-level ``aletheia/__init__.py`` facade.  Keeping this list
# explicit (rather than relying on ``*`` re-export) means a private helper
# added below does not accidentally leak into the binding API surface, and
# consumers get a stable grep target for the cross-binding protocol vocabulary.
__all__ = [
    "AckResponse",
    "AlwaysFormula",
    "AndFormula",
    "AtomicFormula",
    "AttrScope",
    "BetweenPredicate",
    # Literals
    "ByteOrder",
    "ChangedByPredicate",
    # Commands
    "Command",
    "CompleteResponse",
    "CompleteWarning",
    "DBCAttrAssign",
    "DBCAttrDef",
    "DBCAttrDefault",
    "DBCAttrTarget",
    "DBCAttrTargetEnvVar",
    "DBCAttrTargetMessage",
    "DBCAttrTargetNetwork",
    "DBCAttrTargetNode",
    "DBCAttrTargetNodeMsg",
    "DBCAttrTargetNodeSig",
    "DBCAttrTargetSignal",
    "DBCAttrType",
    "DBCAttrTypeEnum",
    "DBCAttrTypeFloat",
    "DBCAttrTypeHex",
    "DBCAttrTypeInt",
    "DBCAttrTypeString",
    "DBCAttrValue",
    "DBCAttrValueEnum",
    "DBCAttrValueFloat",
    "DBCAttrValueHex",
    "DBCAttrValueInt",
    "DBCAttrValueString",
    "DBCAttribute",
    "DBCComment",
    "DBCCommentTarget",
    "DBCCommentTargetEnvVar",
    "DBCCommentTargetMessage",
    "DBCCommentTargetNetwork",
    "DBCCommentTargetNode",
    "DBCCommentTargetSignal",
    "DBCDefinition",
    "DBCEnvironmentVar",
    "DBCMessage",
    # Tier 2 DBC metadata
    "DBCNode",
    "DBCRawValueDesc",
    # DBC types
    "DBCSignal",
    "DBCSignalAlways",
    "DBCSignalGroup",
    "DBCSignalMultiplexed",
    "DBCTextResponse",
    "DBCValueEntry",
    "DBCValueTable",
    "DBCVarType",
    "DLCByteCount",
    "DLCCode",
    "EqualsPredicate",
    "ErrorResponse",
    "EventuallyFormula",
    "ExtractSignalsResponse",
    "FormatDBCResponse",
    "FormatDBCTextCommand",
    "GreaterThanOrEqualPredicate",
    "GreaterThanPredicate",
    # LTL formulas
    "LTLFormula",
    "LessThanOrEqualPredicate",
    "LessThanPredicate",
    "MetricAlwaysFormula",
    "MetricEventuallyFormula",
    "MetricReleaseFormula",
    "MetricUntilFormula",
    "NextFormula",
    "NotFormula",
    "OrFormula",
    "ParseDBCCommand",
    "ParseDBCTextCommand",
    "ParsedDBCResponse",
    # Enums
    "PredicateType",
    "PropertyBatchResponse",
    "PropertyResultEntry",
    # Rational / signal values
    "RationalNumber",
    "ReleaseFormula",
    # Responses
    "Response",
    "SetPropertiesCommand",
    "SignalError",
    # Signal predicates
    "SignalPredicate",
    "SignalPresence",
    "SignalValue",
    "StableWithinPredicate",
    "SuccessResponse",
    "UntilFormula",
    "ValidateDBCCommand",
    "ValidationResponse",
    "ViolationEnrichment",
    "WeakNextFormula",
    "is_object_list",
    # Type guards
    "is_str_dict",
]
