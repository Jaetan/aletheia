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
from typing import TYPE_CHECKING, cast

from aletheia.client._helpers.dbc_normalize import normalize_dbc
from aletheia.client._helpers.rational import validate_integer_field
from aletheia.client._log import LogEvent, log_event
from aletheia.client._refusal import (
    extract_bound_triple,
    raise_if_input_bound_exceeded,
)
from aletheia.client._types import (
    DBCValidationFailedError,
    ProtocolError,
    TextRoundTripFailedError,
)
from aletheia.common_types import Prose
from aletheia.limits import BoundField
from aletheia.types import (
    AckResponse,
    CompleteWarning,
    ErrorResponse,
    ParsedDBCResponse,
    PropertyBatchResponse,
    PropertyResultEntry,
    Response,
    SuccessResponse,
    is_object_list,
    is_str_dict,
)

if TYPE_CHECKING:
    from collections.abc import Callable

    from aletheia.codes import ValidationIssue

_logger = logging.getLogger("aletheia")


def validate_issue_severities(issues: list[ValidationIssue]) -> list[ValidationIssue]:
    """Check each issue is an object with a string severity; return the list unchanged.

    The kernel proves every severity it writes ``"error"`` or ``"warning"``, so
    the reader holds only the kind.

    Raises:
        ProtocolError: If an issue is not an object, or its ``severity`` is
            absent or not a string.

    """
    for issue in issues:
        if not is_str_dict(issue):
            msg = f"Expected validation issue to be an object, got {type(issue).__name__}"
            raise ProtocolError(msg)
        sev = issue.get("severity")
        if not isinstance(sev, str):
            msg = f"Expected string 'severity' in validation issue, got {type(sev).__name__}"
            raise ProtocolError(msg)
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
            not such an object.

    """
    code = response.get("code")
    has_errors = response.get("has_errors")
    if not isinstance(has_errors, bool):
        msg = f"Expected bool 'has_errors' in {code} error reply, got {type(has_errors).__name__}"
        raise ProtocolError(msg)
    raw_issues = response.get("issues")
    if not is_object_list(raw_issues):
        msg = f"Expected 'issues' to be a list in {code} error reply"
        raise ProtocolError(msg)
    if not all(
        is_str_dict(item)
        and isinstance(item.get("code"), str)
        and isinstance(item.get("detail"), str)
        for item in raw_issues
    ):
        msg = (
            "Expected every 'issues' entry to be an object with string 'code' and"
            f" 'detail' in {code} error reply"
        )
        raise ProtocolError(msg)
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
    third-party tooling writing to the same queue) and is surfaced as a
    ``ProtocolError`` rather than papered over with a default.

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
    code = response.get("code")
    if not isinstance(code, str):
        raise ProtocolError(
            "Error response missing or non-string 'code' field;" + f" got {type(code).__name__}"
        )
    message = response.get("message")
    if not isinstance(message, str):
        raise ProtocolError(
            "Error response missing or non-string 'message' field;"
            + f" got {type(message).__name__}"
        )
    out: ErrorResponse = {"status": "error", "code": code, "message": message}
    triple = extract_bound_triple(response)
    if triple is not None:
        out["bound_kind"], out["observed"], out["limit"] = triple
        field = response.get("field")
        if isinstance(field, str):
            out["field"] = BoundField(field)
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

    msg = f"Unexpected response status: {status!r} (expected 'success' or 'error')"
    raise ProtocolError(msg)


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
        dbc_field = response.get("dbc")
        warnings_field = response.get("warnings")
        if not is_str_dict(dbc_field):
            msg = "parseDBC success response missing 'dbc' object"
            raise ProtocolError(msg)
        if warnings_field is None:
            msg = "Expected 'warnings' in parseDBC success reply"
            raise ProtocolError(msg)
        if not is_object_list(warnings_field):
            msg = "parseDBC success response 'warnings' must be a list of objects"
            raise ProtocolError(msg)
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
            "warnings": validate_issue_severities(warnings),
        }

    if status == "error":
        raise_if_input_bound_exceeded(response)
        return build_error_response(response)

    msg = f"Unexpected response status: {status!r} (expected 'success' or 'error')"
    raise ProtocolError(msg)


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
    no-event frame returns `AckResponse` ({"status": "ack"}).
    """
    status = response.get("status")

    if status == "ack":
        return {"status": "ack"}

    if status == "error":
        return build_error_response(response)

    # Streaming PropertyResponse is uniformly a batch with
    # `type="property_batch"`.  No top-level `status` field on the wire —
    # the inner results carry per-event status (fails/holds/unresolved).
    response_type = response.get("type")
    if response_type == "property_batch":
        raw_results = response.get("results")
        if not is_object_list(raw_results):
            msg = "property_batch response missing 'results' array"
            raise ProtocolError(msg)
        parsed_results: list[PropertyResultEntry] = []
        for raw_item in raw_results:
            if not is_str_dict(raw_item):
                msg = "property_batch 'results' entry must be a JSON object"
                raise ProtocolError(msg)
            parsed_results.append(_parse_property_event(cast("dict[str, object]", raw_item)))
        return {"type": "property_batch", "results": parsed_results}

    msg = (
        f"Unexpected response status/type: status={status!r}, type={response_type!r}"
        " (expected 'ack', 'error', or type='property_batch')"
    )
    raise ProtocolError(msg)


def _parse_property_event(raw: dict[str, object]) -> PropertyResultEntry:
    """Parse one inner property event from a property_batch response.

    Inner shape mirrors EndStream's `PropertyResultEntry`:
        {"type": "property", "status": "fails"|"holds"|"unresolved",
         "property_index": int, "timestamp": int?, "reason": str?}

    The kernel proves ``type`` and ``status`` in those sets, so the reader
    checks their kind and casts them; any status but ``fails`` and ``holds``
    is read as ``unresolved``.  A ``fails`` event carries ``timestamp``, and a
    ``fails`` or ``unresolved`` event carries ``reason``, refused when absent.
    """
    inner_type = raw.get("type")
    if not isinstance(inner_type, str):
        msg = f"Expected string 'type' in property_batch event, got {type(inner_type).__name__}"
        raise ProtocolError(msg)
    inner_status = raw.get("status")
    if not isinstance(inner_status, str):
        msg = f"Expected string 'status' in property_batch event, got {type(inner_status).__name__}"
        raise ProtocolError(msg)
    prop_index = validate_integer_field("property_index", raw.get("property_index"))
    entry = cast(
        "PropertyResultEntry",
        {"type": inner_type, "status": inner_status, "property_index": prop_index},
    )
    if inner_status == "fails":
        entry["timestamp"] = validate_integer_field("timestamp", raw.get("timestamp"))
    if inner_status != "holds":
        reason = raw.get("reason")
        if not isinstance(reason, str):
            msg = f"Expected string 'reason' in property_batch {inner_status!r} event"
            raise ProtocolError(msg)
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
        msg = f"Expected string 'reason' in {entry['status']!r} result entry"
        raise ProtocolError(msg)
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
    msg = f"Unexpected {event_kind} response status: {status!r} (expected 'ack' or 'error')"
    raise ProtocolError(msg)


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
    ``fails`` and ``holds`` is read as ``unresolved``.
    """
    results_raw = response.get("results")
    if not is_object_list(results_raw):
        msg = "Missing or invalid 'results' in finalization response"
        raise ProtocolError(msg)
    entries: list[PropertyResultEntry] = []
    for raw in results_raw:
        if not is_str_dict(raw):
            msg = f"Expected finalization result entry to be an object, got {type(raw).__name__}"
            raise ProtocolError(msg)
        entry_status = raw.get("status")
        if not isinstance(entry_status, str):
            msg = (
                "Expected string 'status' in finalization result entry,"
                f" got {type(entry_status).__name__}"
            )
            raise ProtocolError(msg)
        raw_prop_index = raw.get("property_index")
        if raw_prop_index is None:
            msg = "Missing 'property_index' in finalization result entry"
            raise ProtocolError(msg)
        prop_index = validate_integer_field("property_index", raw_prop_index)
        result_entry = cast(
            "PropertyResultEntry",
            {"type": "property", "status": entry_status, "property_index": prop_index},
        )
        if entry_status != "holds":
            ts = raw.get("timestamp")
            if ts is not None:
                result_entry["timestamp"] = validate_integer_field("timestamp", ts)
            elif entry_status == "fails":
                msg = "Expected 'timestamp' in finalization result entry with status 'fails'"
                raise ProtocolError(msg)
            reason = raw.get("reason")
            if not isinstance(reason, str):
                msg = (
                    "Expected string 'reason' in finalization result entry"
                    f" with status {entry_status!r}"
                )
                raise ProtocolError(msg)
            result_entry["reason"] = reason
            enrich(result_entry)
        entries.append(result_entry)
    return entries


def parse_complete_warnings(response: Response) -> list[CompleteWarning]:
    """Parse the ``warnings`` list of an end-of-stream ``complete`` response.

    Mirrors :func:`parse_finalization_results`' defensive parsing: the FFI
    JSON is untrusted, so the ``warnings`` field must be a list and each
    entry an object (else a typed :class:`ProtocolError`, not a bare
    ``TypeError``/``AttributeError``), and ``property_index`` is run through
    :func:`validate_integer_field` (which accepts the plain-int and
    ``{"numerator": N, "denominator": 1}`` wire shapes and rejects a
    non-integer, non-unit-denominator, or wrong-typed value) rather than
    blindly ``cast``. Go's ``parseNumberAsInt64`` and the per-entry
    ``item.(map[string]any)`` check raise on the same inputs. The kernel
    writes ``warnings`` and each entry's ``kind``, ``property_index`` and
    ``detail``, so a missing one is a protocol violation and is rejected
    rather than silently defaulted.
    """
    raw_warnings = response.get("warnings")
    if raw_warnings is None:
        msg = "Expected 'warnings' in end-of-stream complete reply"
        raise ProtocolError(msg)
    if not is_object_list(raw_warnings):
        msg = "'warnings' must be a list in end-of-stream complete response"
        raise ProtocolError(msg)
    warnings: list[CompleteWarning] = []
    for raw in raw_warnings:
        if not is_str_dict(raw):
            msg = "end-of-stream warning entry must be an object"
            raise ProtocolError(msg)
        kind = raw.get("kind")
        if not isinstance(kind, str):
            msg = (
                f"Expected string 'kind' in end-of-stream warning entry, got {type(kind).__name__}"
            )
            raise ProtocolError(msg)
        raw_prop_index = raw.get("property_index")
        if raw_prop_index is None:
            msg = "Missing 'property_index' in end-of-stream warning entry"
            raise ProtocolError(msg)
        detail = raw.get("detail")
        if not isinstance(detail, str):
            msg = (
                "Expected string 'detail' in end-of-stream warning entry,"
                f" got {type(detail).__name__}"
            )
            raise ProtocolError(msg)
        warnings.append(
            cast(
                "CompleteWarning",
                {
                    "kind": kind,
                    "property_index": validate_integer_field("property_index", raw_prop_index),
                    "detail": detail,
                },
            )
        )
    return warnings
