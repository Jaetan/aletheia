# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Response parsers — turn raw FFI JSON dicts into typed response objects.

Pure functions, stateless. Extracted from ``_client.py`` so the
``AletheiaClient`` module stays under pylint's 1000-line cap. The client
delegates to these helpers for the repetitive "decode a Response dict into
the right typed shape" logic; finalization parsing takes a callback so the
enrichment step (which needs ``self._diags``/``self._caches``) remains on
the client.
"""

import logging
from typing import TYPE_CHECKING

from aletheia.client._helpers.dbc_normalize import normalize_dbc
from aletheia.client._helpers.rational import is_pure_int
from aletheia.client._helpers.reply_shape import (
    ARRAY,
    BOOLEAN,
    NUMBER,
    OBJECT,
    REPLY_ROOT,
    STRING,
    Expectation,
    at,
    came,
    came_as,
    came_word,
    field_member,
    field_word,
    held,
    reply_refusal,
    words,
)
from aletheia.client._log import LogEvent, log_event
from aletheia.client._refusal import (
    bound_field,
    extract_bound_triple,
    raise_if_input_bound_exceeded,
    read_error_code,
)
from aletheia.client._types import (
    DBCValidationFailedError,
    ProtocolError,
    TextRoundTripFailedError,
)
from aletheia.codes import ErrorCode, IssueCode, IssueSeverity
from aletheia.common_types import Prose
from aletheia.types import (
    AckResponse,
    CompleteWarning,
    ErrorResponse,
    ParsedDBCResponse,
    PropertyBatchResponse,
    PropertyResultEntry,
    SuccessResponse,
    is_str_dict,
)

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.client._helpers.reply_shape import ReplyFields, ReplyPath
    from aletheia.codes import ValidationIssue
    from aletheia.types import JSONValue

_logger = logging.getLogger("aletheia")

# The reply places more than one reader names.
_STATUS = at(REPLY_ROOT, "status")
_RESULTS = at(REPLY_ROOT, "results")
_WARNINGS = at(REPLY_ROOT, "warnings")
_ISSUES = at(REPLY_ROOT, "issues")

_AN_ISSUE_CODE = Expectation("an issue code")


def read_issues(raw: list[JSONValue], path: ReplyPath = _ISSUES) -> list[ValidationIssue]:
    """Read the issues at ``path``: ``issues``, or ``warnings`` in a parseDBC reply.

    Each is an object holding its ``code``, one of the :class:`IssueCode`
    words, its ``detail``, a string, and its ``severity``, ``"error"`` or
    ``"warning"``; the two words are read as the members they name.

    Raises:
        ProtocolError: If an issue is not an object, its code or severity is
            not one of its words, or its detail is not a string, refused at its
            place.

    """
    return [_read_issue(issue, path) for issue in raw]


def _read_issue(issue: JSONValue, path: ReplyPath) -> ValidationIssue:
    """Read one issue at ``path``, its code first, then its detail and its severity."""
    if not is_str_dict(issue):
        raise reply_refusal(path, OBJECT, came_as(issue))
    code = field_member(issue, path, "code", IssueCode, _AN_ISSUE_CODE)
    detail = held(issue, "detail")
    if not isinstance(detail, str):
        raise reply_refusal(at(path, "detail"), STRING, came(issue, "detail"))
    severity = IssueSeverity(field_word(issue, path, "severity", "error", "warning"))
    return {"severity": severity, "code": code, "detail": detail}


# The error envelopes that carry a structured issues / has_errors payload
# (appended by ``Protocol/ResponseFormat.errorExtras``): ``handler_validation_failed``
# from parseDBC / parseDBCText, ``handler_text_roundtrip_failed`` from formatDBCText.
# build_error_response attaches the payload for ANY of these; each typed-error lift
# gates on a single one.
ISSUES_CARRYING_CODES = frozenset({"handler_validation_failed", "handler_text_roundtrip_failed"})


def _extract_issues_payload(
    reply: ReplyFields,
) -> tuple[list[ValidationIssue], bool]:
    """Extract the ``issues`` / ``has_errors`` pair from an envelope, without gating on code.

    The kernel writes both fields on every envelope whose code is in
    :data:`ISSUES_CARRYING_CODES`, every issue one :func:`read_issues` reads.

    Raises:
        ProtocolError: If either field is absent or ill-typed, or an issue is
            one :func:`read_issues` refuses, refused at its place.

    """
    has_errors = held(reply, "has_errors")
    if not isinstance(has_errors, bool):
        raise reply_refusal(at(REPLY_ROOT, "has_errors"), BOOLEAN, came(reply, "has_errors"))
    raw_issues = held(reply, "issues")
    if not isinstance(raw_issues, list):
        raise reply_refusal(_ISSUES, ARRAY, came(reply, "issues"))
    return read_issues(raw_issues), has_errors


def lift_issues_envelope(
    response: ReplyFields,
    code: str,
) -> tuple[list[ValidationIssue], bool] | None:
    """Extract the ``issues`` / ``has_errors`` pair from an error envelope gated on ``code``.

    Gating on the wire code, like the Go / C++ / Rust decoders, keeps another
    error envelope that happens to carry has_errors/issues-shaped keys from being
    mis-lifted into the wrong typed error.

    Raises:
        ProtocolError: If the envelope carries ``code`` with an ill-formed pair
            (see :func:`_extract_issues_payload`).

    """
    if held(response, "code") != code:
        return None
    return _extract_issues_payload(response)


def raise_if_dbc_validation_failed(response: ReplyFields, msg: str) -> None:
    """Raise :class:`DBCValidationFailedError` for a structured DBC validation failure.

    Returns normally when ``response`` carries another code, so the caller raises
    its own fallback (``ProtocolError`` on the client, ``ValidationError`` in the
    converter). The single lift-and-raise shared by the client's DBC routes and
    the ``dbc`` converter: one wire-code gate, no per-caller re-implementation.

    Raises:
        DBCValidationFailedError: If ``response`` is a validation failure.
        ProtocolError: If it carries the code with an ill-formed issues payload.

    """
    lifted = lift_issues_envelope(response, "handler_validation_failed")
    if lifted is not None:
        issues, has_errors = lifted
        raise DBCValidationFailedError(
            msg, issues, has_errors=has_errors, code=ErrorCode.HANDLER_VALIDATION_FAILED
        )


def raise_if_text_roundtrip_failed(response: ReplyFields, msg: str) -> None:
    """Raise :class:`TextRoundTripFailedError` for a ``format_dbc_text`` round-trip refusal.

    Returns normally when ``response`` carries another code, so the caller raises
    its own generic fallback.  Mirrors
    :func:`raise_if_dbc_validation_failed` for the ``handler_text_roundtrip_failed``
    wire code — same lift, distinct typed error.

    Raises:
        TextRoundTripFailedError: If ``response`` is a round-trip refusal.
        ProtocolError: If it carries the code with an ill-formed issues payload.

    """
    lifted = lift_issues_envelope(response, "handler_text_roundtrip_failed")
    if lifted is not None:
        issues, has_errors = lifted
        raise TextRoundTripFailedError(
            msg, issues, has_errors=has_errors, code=ErrorCode.HANDLER_TEXT_ROUNDTRIP_FAILED
        )


def build_error_response(response: ReplyFields) -> ErrorResponse:
    """Build an ``ErrorResponse`` from a raw FFI response dict.

    The Agda core always emits ``code``, one of the :class:`ErrorCode`
    words, read as the member it names, and ``message``, a string, on
    ``status = "error"``. Any other ``code`` or ``message`` indicates a
    malformed response (FFI drift, hand-crafted test stub, or third-party
    tooling writing to the same queue) and is refused at its place rather
    than papered over with a default.

    InputBoundExceeded errors carry an additional ``bound_kind`` /
    ``observed`` / ``limit`` triple via ``Protocol/ResponseFormat.
    errorExtras``; all three must be present and well-typed when any
    one is, else the payload is treated as missing rather than partial
    (see :func:`~aletheia.client._refusal.extract_bound_triple`).

    Validation-failure errors carry the ``issues`` / ``has_errors`` pair,
    which the kernel writes on every code in :data:`ISSUES_CARRYING_CODES`;
    an ill-formed pair is a ``ProtocolError`` (see
    :func:`_extract_issues_payload`).
    """
    code = read_error_code(response)
    message = held(response, "message")
    if not isinstance(message, str):
        raise reply_refusal(at(REPLY_ROOT, "message"), STRING, came(response, "message"))
    out: ErrorResponse = {"status": "error", "code": code, "message": message}
    triple = extract_bound_triple(response)
    if triple is not None:
        out["bound_kind"], out["observed"], out["limit"] = triple
        if (field := bound_field(response)) is not None:
            out["field"] = field
    if code in ISSUES_CARRYING_CODES:
        out["issues"], out["has_errors"] = _extract_issues_payload(response)
    return out


def parse_success_or_error(
    response: ReplyFields,
) -> SuccessResponse | ErrorResponse:
    """Parse a response that should be success or error."""
    status = held(response, "status")

    if status == "success":
        result: SuccessResponse = {"status": "success"}
        message = held(response, "message")
        if isinstance(message, str):
            result["message"] = message
        return result

    if status == "error":
        return build_error_response(response)

    raise reply_refusal(_STATUS, words("success", "error"), came_word(response, "status"))


def parse_parsed_dbc_response(
    response: ReplyFields,
) -> ParsedDBCResponse | ErrorResponse:
    """Parse a response from parseDBC / parseDBCText.

    On success the Agda core emits ``ParsedDBCResponse`` carrying the
    canonical parsed body plus any non-error issues (warnings).  On
    failure it emits an error with a typed code: a bound refusal raises
    :class:`InputBoundExceededError`, any other returns the ``ErrorResponse``.
    """
    status = held(response, "status")

    if status == "success":
        dbc_field = held(response, "dbc")
        if not is_str_dict(dbc_field):
            raise reply_refusal(at(REPLY_ROOT, "dbc"), OBJECT, came(response, "dbc"))
        warnings_field = held(response, "warnings")
        if not isinstance(warnings_field, list):
            raise reply_refusal(_WARNINGS, ARRAY, came(response, "warnings"))
        # Agda emits non-integer rationals on the wire as
        # ``{"numerator": n, "denominator": d}`` dicts; ``normalize_dbc``
        # converts those back to ``Fraction`` so callers see a real
        # ``DBCDefinition`` instead of a typed-cast lie. This is the
        # symmetry of ``FractionJSONEncoder`` on the request side, and
        # mirrors what Go's ``parseRational`` and the C++ JSON deserialiser
        # already do — the asymmetry was a Python-side bug surfaced by
        # the switch to the Agda-backed ``dbc_to_json`` default.
        return {
            "status": "success",
            "dbc": normalize_dbc(dbc_field),
            "warnings": read_issues(warnings_field, _WARNINGS),
        }

    if status == "error":
        raise_if_input_bound_exceeded(response)
        return build_error_response(response)

    raise reply_refusal(_STATUS, words("success", "error"), came_word(response, "status"))


def parse_frame_response(
    response: ReplyFields,
) -> AckResponse | PropertyBatchResponse | ErrorResponse:
    """Parse a single frame response into a typed result.

    A single frame may produce a batch of property events (any
    satisfactions that completed before a halting violation, in
    source-order, followed by the violation).  The wire `type` is
    `"property_batch"`; the `results` list holds the
    `PropertyResultEntry` objects (fails / holds / unresolved), at least
    one, as the kernel proves, so the reader does not check it.  A
    no-event frame returns `AckResponse` ({"status": "ack"}).  A reply
    whose ``status`` is neither ``ack`` nor ``error`` is refused at
    ``status``; one without ``status`` is read as a batch by its ``type``.
    """
    status = held(response, "status")

    if status == "ack":
        return {"status": "ack"}

    if status == "error":
        return build_error_response(response)

    # A property batch carries no top-level `status`; its entries carry
    # each event's own (fails/holds/unresolved).
    if "status" in response:
        raise reply_refusal(_STATUS, words("ack", "error"), came_word(response, "status"))
    if held(response, "type") != "property_batch":
        raise reply_refusal(
            at(REPLY_ROOT, "type"), words("property_batch"), came_word(response, "type")
        )
    raw_results = held(response, "results")
    if not isinstance(raw_results, list):
        raise reply_refusal(_RESULTS, ARRAY, came(response, "results"))
    parsed_results: list[PropertyResultEntry] = []
    for raw_item in raw_results:
        if not is_str_dict(raw_item):
            raise reply_refusal(_RESULTS, OBJECT, came_as(raw_item))
        parsed_results.append(_parse_property_event(raw_item))
    return {"type": "property_batch", "results": parsed_results}


def _read_result(raw: ReplyFields) -> PropertyResultEntry:
    """Read the ``type``, ``status`` and ``property_index`` every property result carries.

    Each is read in that order and refused at its place: ``type`` is
    ``property``, ``status`` one of ``fails``, ``holds`` and ``unresolved``,
    ``property_index`` a whole number.  The timestamp and the reason are the
    caller's to read.
    """
    result_type = field_word(raw, _RESULTS, "type", "property")
    status = field_word(raw, _RESULTS, "status", "fails", "holds", "unresolved")
    prop_index = held(raw, "property_index")
    if not is_pure_int(prop_index):
        raise reply_refusal(at(_RESULTS, "property_index"), NUMBER, came(raw, "property_index"))
    return {"type": result_type, "status": status, "property_index": prop_index}


def _parse_property_event(raw: ReplyFields) -> PropertyResultEntry:
    """Parse one event of a property_batch response.

    A ``fails`` event carries ``timestamp``, and a ``fails`` or ``unresolved``
    event carries ``reason``, refused when absent.
    """
    entry = _read_result(raw)
    inner_status = entry["status"]
    if inner_status == "fails":
        timestamp = held(raw, "timestamp")
        if not is_pure_int(timestamp):
            raise reply_refusal(at(_RESULTS, "timestamp"), NUMBER, came(raw, "timestamp"))
        entry["timestamp"] = timestamp
    if inner_status != "holds":
        reason = held(raw, "reason")
        if not isinstance(reason, str):
            raise reply_refusal(at(_RESULTS, "reason"), STRING, came(raw, "reason"))
        entry["reason"] = reason
    return entry


def entry_reason(entry: PropertyResultEntry) -> Prose:
    """Return the ``reason`` of a ``fails`` or ``unresolved`` result entry.

    The parsers refuse such an entry without one, so only an entry built
    without them can lack it.

    Raises:
        ProtocolError: The entry carries no ``reason``.

    """
    reason = entry.get("reason")
    if reason is None:
        raise reply_refusal(at(_RESULTS, "reason"), STRING, came(entry, "reason"))
    return Prose(reason)


def parse_event_response(
    response: ReplyFields,
    event_kind: str,
    timestamp: int,
) -> AckResponse:
    """Parse a non-data-frame event response (error/remote frames).

    These events cannot trigger property violations, so only ack and
    error responses are expected.  An ``ErrorResponse`` (e.g. non-monotonic
    timestamp) is raised as a ``ProtocolError`` rather than returned,
    matching Go (returns ``error``) and C++ (returns ``Result<void>``).
    """
    # Map the caller's ``event_kind`` onto the canonical structured event
    # name.  Only ``"error_event"`` and ``"remote_event"`` are accepted; any
    # new kind must be added to ``LogEvent`` first so the cross-binding
    # observability vocabulary stays stable.
    event_map = {
        "error_event": LogEvent.ERROR_EVENT_SENT,
        "remote_event": LogEvent.REMOTE_EVENT_SENT,
    }
    event = event_map.get(event_kind)
    if event is None:
        msg = f"Unknown event_kind {event_kind!r}"
        raise ProtocolError(msg)

    status = held(response, "status")
    # Trace events (Error/Remote) always resolve to `Response.Ack` in Agda
    # (see Protocol/StreamState.agda handleTraceEvent), so the wire status is
    # always "ack". Tightened to match the Agda protocol exactly — Go
    # parseEventAck and C++ parse_event_ack enforce the same.
    if status == "ack":
        log_event(
            _logger,
            logging.DEBUG,
            event,
            ts=timestamp,
            response="ack",
        )
        return {"status": "ack"}
    if status == "error":
        result_error = build_error_response(response)
        log_event(
            _logger,
            logging.DEBUG,
            event,
            ts=timestamp,
            response="error",
            code=result_error["code"],
        )
        raise ProtocolError(result_error["message"], code=result_error["code"])
    raise reply_refusal(_STATUS, words("ack", "error"), came_word(response, "status"))


def parse_finalization_results(
    response: ReplyFields,
    enrich: Callable[[PropertyResultEntry], None],
) -> list[PropertyResultEntry]:
    """Parse end-of-stream property finalization results.

    ``enrich`` is invoked once per ``fails``/``unresolved`` entry so the
    client can attach an ``enrichment`` field (signals, formula_desc,
    enriched_reason, core_reason) using its own diagnostic and cache state.
    A ``fails`` entry carries ``timestamp``, which an ``unresolved`` one may
    carry too.
    """
    results_raw = held(response, "results")
    if not isinstance(results_raw, list):
        raise reply_refusal(_RESULTS, ARRAY, came(response, "results"))
    entries: list[PropertyResultEntry] = []
    for raw in results_raw:
        if not is_str_dict(raw):
            raise reply_refusal(_RESULTS, OBJECT, came_as(raw))
        result_entry = _read_result(raw)
        entry_status = result_entry["status"]
        if entry_status != "holds":
            ts = raw.get("timestamp")
            if is_pure_int(ts):
                result_entry["timestamp"] = ts
            elif ts is not None or entry_status == "fails":
                raise reply_refusal(at(_RESULTS, "timestamp"), NUMBER, came(raw, "timestamp"))
            reason = raw.get("reason")
            if not isinstance(reason, str):
                raise reply_refusal(at(_RESULTS, "reason"), STRING, came(raw, "reason"))
            result_entry["reason"] = reason
            enrich(result_entry)
        entries.append(result_entry)
    return entries


def parse_complete_warnings(response: ReplyFields) -> list[CompleteWarning]:
    """Parse the ``warnings`` list of an end-of-stream ``complete`` response.

    The kernel writes ``warnings`` and each entry's ``kind``,
    ``property_index`` and ``detail``, so a place missing or holding another
    kind is refused at its place rather than defaulted or cast: ``kind`` is
    ``uncached_atom``, ``property_index`` a whole number written as digits.
    """
    raw_warnings = held(response, "warnings")
    if not isinstance(raw_warnings, list):
        raise reply_refusal(_WARNINGS, ARRAY, came(response, "warnings"))
    warnings: list[CompleteWarning] = []
    for raw in raw_warnings:
        if not is_str_dict(raw):
            raise reply_refusal(_WARNINGS, OBJECT, came_as(raw))
        kind = field_word(raw, _WARNINGS, "kind", "uncached_atom")
        prop_index = raw.get("property_index")
        if not is_pure_int(prop_index):
            raise reply_refusal(
                at(_WARNINGS, "property_index"), NUMBER, came(raw, "property_index")
            )
        detail = raw.get("detail")
        if not isinstance(detail, str):
            raise reply_refusal(at(_WARNINGS, "detail"), STRING, came(raw, "detail"))
        warnings.append({"kind": kind, "property_index": prop_index, "detail": detail})
    return warnings
