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
from typing import TYPE_CHECKING, LiteralString, cast

from aletheia.client._helpers.dbc_normalize import normalize_dbc
from aletheia.client._helpers.rational import is_pure_int
from aletheia.client._helpers.reply_shape import (
    ARRAY,
    BOOLEAN,
    NUMBER,
    OBJECT,
    REPLY_ROOT,
    STRING,
    at,
    came,
    came_as,
    came_word,
    fields,
    reply_refusal,
    words,
)
from aletheia.client._log import LogEvent, log_event
from aletheia.client._refusal import (
    bound_field,
    extract_bound_triple,
    raise_if_input_bound_exceeded,
)
from aletheia.client._types import (
    DBCValidationFailedError,
    ProtocolError,
    TextRoundTripFailedError,
)
from aletheia.common_types import Prose
from aletheia.types import (
    AckResponse,
    CompleteWarning,
    ErrorResponse,
    ParsedDBCResponse,
    PropertyBatchResponse,
    PropertyResultEntry,
    Response,
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


def _held(obj: ReplyFields, key: LiteralString) -> JSONValue:
    """Read ``key`` of a reply object: its value, or ``None`` when the object lacks it."""
    if key not in obj:
        return None
    return obj[key]


def validate_issue_severities(
    issues: list[ValidationIssue], path: ReplyPath = _ISSUES
) -> list[ValidationIssue]:
    """Check each issue is an object with a string severity; return the list unchanged.

    The kernel proves every severity it writes ``"error"`` or ``"warning"``, so
    the reader holds only the kind. ``path`` is the issues' place: ``issues``,
    or ``warnings`` in a parseDBC reply.

    Raises:
        ProtocolError: If an issue is not an object, or its ``severity`` is
            absent or not a string, refused at its place.

    """
    for issue in cast("list[JSONValue]", issues):
        if not is_str_dict(issue):
            raise reply_refusal(path, OBJECT, came_as(issue))
        if not isinstance(issue.get("severity"), str):
            raise reply_refusal(at(path, "severity"), STRING, came(issue, "severity"))
    return issues


# The error envelopes that carry a structured issues / has_errors payload
# (appended by ``Protocol/ResponseFormat.errorExtras``): ``handler_validation_failed``
# from parseDBC / parseDBCText, ``handler_text_roundtrip_failed`` from formatDBCText.
# build_error_response attaches the payload for ANY of these; each typed-error lift
# gates on a single one.
ISSUES_CARRYING_CODES = frozenset({"handler_validation_failed", "handler_text_roundtrip_failed"})


def _extract_issues_payload(
    response: Response,
) -> tuple[list[ValidationIssue], bool]:
    """Extract the ``issues`` / ``has_errors`` pair from an envelope, without gating on code.

    The kernel writes both fields on every envelope whose code is in
    :data:`ISSUES_CARRYING_CODES`, every issue an object with string
    ``severity``, ``code`` and ``detail``.

    Raises:
        ProtocolError: If either field is absent or ill-typed, or an issue is
            not such an object, refused at its place.

    """
    reply = fields(response)
    has_errors = response.get("has_errors")
    if not isinstance(has_errors, bool):
        raise reply_refusal(at(REPLY_ROOT, "has_errors"), BOOLEAN, came(reply, "has_errors"))
    raw_issues = _held(reply, "issues")
    if not isinstance(raw_issues, list):
        raise reply_refusal(_ISSUES, ARRAY, came(reply, "issues"))
    for item in raw_issues:
        if not is_str_dict(item):
            raise reply_refusal(_ISSUES, OBJECT, came_as(item))
        if not isinstance(item.get("code"), str):
            raise reply_refusal(at(_ISSUES, "code"), STRING, came(item, "code"))
        if not isinstance(item.get("detail"), str):
            raise reply_refusal(at(_ISSUES, "detail"), STRING, came(item, "detail"))
    issues = cast("list[ValidationIssue]", list(raw_issues))
    return validate_issue_severities(issues), has_errors


def lift_issues_envelope(
    response: Response,
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
    if response.get("code") != code:
        return None
    return _extract_issues_payload(response)


def raise_if_dbc_validation_failed(response: Response, msg: str) -> None:
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
            msg, issues, has_errors=has_errors, code="handler_validation_failed"
        )


def raise_if_text_roundtrip_failed(response: Response, msg: str) -> None:
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
            msg, issues, has_errors=has_errors, code="handler_text_roundtrip_failed"
        )


def build_error_response(response: Response) -> ErrorResponse:
    """Build an ``ErrorResponse`` from a raw FFI response dict.

    The Agda core always emits both ``code`` and ``message`` as strings
    on ``status = "error"``. Either field missing or non-string indicates
    a malformed response (FFI drift, hand-crafted test stub, or
    third-party tooling writing to the same queue) and is refused at its
    place rather than papered over with a default.

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
    reply = fields(response)
    code = response.get("code")
    if not isinstance(code, str):
        raise reply_refusal(at(REPLY_ROOT, "code"), STRING, came(reply, "code"))
    message = response.get("message")
    if not isinstance(message, str):
        raise reply_refusal(at(REPLY_ROOT, "message"), STRING, came(reply, "message"))
    out: ErrorResponse = {"status": "error", "code": code, "message": message}
    triple = extract_bound_triple(response)
    if triple is not None:
        out["bound_kind"], out["observed"], out["limit"] = triple
        if (field := bound_field(response)) is not None:
            out["field"] = field
    if response.get("code") in ISSUES_CARRYING_CODES:
        out["issues"], out["has_errors"] = _extract_issues_payload(response)
    return out


def parse_success_or_error(
    response: Response,
) -> SuccessResponse | ErrorResponse:
    """Parse a response that should be success or error."""
    status = response.get("status")

    if status == "success":
        result: SuccessResponse = {"status": "success"}
        message = response.get("message")
        if isinstance(message, str):
            result["message"] = message
        return result

    if status == "error":
        return build_error_response(response)

    raise reply_refusal(_STATUS, words("success", "error"), came_word(fields(response), "status"))


def parse_parsed_dbc_response(
    response: Response,
) -> ParsedDBCResponse | ErrorResponse:
    """Parse a response from parseDBC / parseDBCText.

    On success the Agda core emits ``ParsedDBCResponse`` carrying the
    canonical parsed body plus any non-error issues (warnings).  On
    failure it emits an error with a typed code: a bound refusal raises
    :class:`InputBoundExceededError`, any other returns the ``ErrorResponse``.
    """
    status = response.get("status")

    if status == "success":
        reply = fields(response)
        dbc_field = response.get("dbc")
        if not is_str_dict(dbc_field):
            raise reply_refusal(at(REPLY_ROOT, "dbc"), OBJECT, came(reply, "dbc"))
        warnings_field = _held(reply, "warnings")
        if not isinstance(warnings_field, list):
            raise reply_refusal(_WARNINGS, ARRAY, came(reply, "warnings"))
        warnings = cast("list[ValidationIssue]", list(warnings_field))
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
            "warnings": validate_issue_severities(warnings, _WARNINGS),
        }

    if status == "error":
        raise_if_input_bound_exceeded(response)
        return build_error_response(response)

    raise reply_refusal(_STATUS, words("success", "error"), came_word(fields(response), "status"))


def parse_frame_response(
    response: Response,
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
    status = response.get("status")

    if status == "ack":
        return {"status": "ack"}

    if status == "error":
        return build_error_response(response)

    # A property batch carries no top-level `status`; its entries carry
    # each event's own (fails/holds/unresolved).
    reply = fields(response)
    if "status" in reply:
        raise reply_refusal(_STATUS, words("ack", "error"), came_word(reply, "status"))
    if response.get("type") != "property_batch":
        raise reply_refusal(
            at(REPLY_ROOT, "type"), words("property_batch"), came_word(reply, "type")
        )
    raw_results = _held(reply, "results")
    if not isinstance(raw_results, list):
        raise reply_refusal(_RESULTS, ARRAY, came(reply, "results"))
    parsed_results: list[PropertyResultEntry] = []
    for raw_item in raw_results:
        if not is_str_dict(raw_item):
            raise reply_refusal(_RESULTS, OBJECT, came_as(raw_item))
        parsed_results.append(_parse_property_event(raw_item))
    return {"type": "property_batch", "results": parsed_results}


def _parse_property_event(raw: ReplyFields) -> PropertyResultEntry:
    """Parse one inner property event from a property_batch response.

    Inner shape mirrors EndStream's `PropertyResultEntry`:
        {"type": "property", "status": "fails"|"holds"|"unresolved",
         "property_index": int, "timestamp": int?, "reason": str?}

    The kernel proves ``type`` and ``status`` in those sets, so the reader
    checks their kind and casts them; any status but ``fails`` and ``holds``
    is read as ``unresolved``.  A ``fails`` event carries ``timestamp``, and a
    ``fails`` or ``unresolved`` event carries ``reason``, refused when absent.
    """
    inner_type = _held(raw, "type")
    if not isinstance(inner_type, str):
        raise reply_refusal(at(_RESULTS, "type"), STRING, came(raw, "type"))
    inner_status = _held(raw, "status")
    if not isinstance(inner_status, str):
        raise reply_refusal(at(_RESULTS, "status"), STRING, came(raw, "status"))
    prop_index = _held(raw, "property_index")
    if not is_pure_int(prop_index):
        raise reply_refusal(at(_RESULTS, "property_index"), NUMBER, came(raw, "property_index"))
    entry = cast(
        "PropertyResultEntry",
        {"type": inner_type, "status": inner_status, "property_index": prop_index},
    )
    if inner_status == "fails":
        timestamp = _held(raw, "timestamp")
        if not is_pure_int(timestamp):
            raise reply_refusal(at(_RESULTS, "timestamp"), NUMBER, came(raw, "timestamp"))
        entry["timestamp"] = timestamp
    if inner_status != "holds":
        reason = _held(raw, "reason")
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
        raise reply_refusal(
            at(_RESULTS, "reason"), STRING, came(cast("ReplyFields", entry), "reason")
        )
    return Prose(reason)


def parse_event_response(
    response: Response,
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

    status = response.get("status")
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
    raise reply_refusal(_STATUS, words("ack", "error"), came_word(fields(response), "status"))


def parse_finalization_results(
    response: Response,
    enrich: Callable[[PropertyResultEntry], None],
) -> list[PropertyResultEntry]:
    """Parse end-of-stream property finalization results.

    ``enrich`` is invoked once per ``fails``/``unresolved`` entry so the
    client can attach an ``enrichment`` field (signals, formula_desc,
    enriched_reason, core_reason) using its own diagnostic and cache state.
    The kernel proves each entry's ``status`` one of ``fails``, ``holds`` and
    ``unresolved``, so the reader checks its kind and casts it; any status but
    ``fails`` and ``holds`` is read as ``unresolved``.  A ``fails`` entry
    carries ``timestamp``, which an ``unresolved`` one may carry too.
    """
    reply = fields(response)
    results_raw = _held(reply, "results")
    if not isinstance(results_raw, list):
        raise reply_refusal(_RESULTS, ARRAY, came(reply, "results"))
    entries: list[PropertyResultEntry] = []
    for raw in results_raw:
        if not is_str_dict(raw):
            raise reply_refusal(_RESULTS, OBJECT, came_as(raw))
        entry_status = raw.get("status")
        if not isinstance(entry_status, str):
            raise reply_refusal(at(_RESULTS, "status"), STRING, came(raw, "status"))
        prop_index = raw.get("property_index")
        if not is_pure_int(prop_index):
            raise reply_refusal(at(_RESULTS, "property_index"), NUMBER, came(raw, "property_index"))
        result_entry = cast(
            "PropertyResultEntry",
            {"type": "property", "status": entry_status, "property_index": prop_index},
        )
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


def parse_complete_warnings(response: Response) -> list[CompleteWarning]:
    """Parse the ``warnings`` list of an end-of-stream ``complete`` response.

    The kernel writes ``warnings`` and each entry's ``kind``,
    ``property_index`` and ``detail``, so a place missing or holding another
    kind is refused at its place rather than defaulted or cast.
    ``property_index`` is a whole number, written as digits.
    """
    reply = fields(response)
    raw_warnings = _held(reply, "warnings")
    if not isinstance(raw_warnings, list):
        raise reply_refusal(_WARNINGS, ARRAY, came(reply, "warnings"))
    warnings: list[CompleteWarning] = []
    for raw in raw_warnings:
        if not is_str_dict(raw):
            raise reply_refusal(_WARNINGS, OBJECT, came_as(raw))
        kind = raw.get("kind")
        if not isinstance(kind, str):
            raise reply_refusal(at(_WARNINGS, "kind"), STRING, came(raw, "kind"))
        prop_index = raw.get("property_index")
        if not is_pure_int(prop_index):
            raise reply_refusal(
                at(_WARNINGS, "property_index"), NUMBER, came(raw, "property_index")
            )
        detail = raw.get("detail")
        if not isinstance(detail, str):
            raise reply_refusal(at(_WARNINGS, "detail"), STRING, came(raw, "detail"))
        warnings.append(
            cast(
                "CompleteWarning",
                {"kind": kind, "property_index": prop_index, "detail": detail},
            )
        )
    return warnings
