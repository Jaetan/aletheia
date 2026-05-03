"""Response parsers — turn raw FFI JSON dicts into typed response objects.

Pure functions, stateless. Extracted from ``_client.py`` so the
``AletheiaClient`` module stays under pylint's 1000-line cap. The client
delegates to these helpers for the repetitive "decode a Response dict into
the right typed shape" logic; finalization parsing takes a callback so the
enrichment step (which needs ``self._diags``/``self._caches``) remains on
the client.
"""

import logging
from collections.abc import Callable
from typing import cast

from ..protocols import (
    AckResponse,
    ErrorResponse,
    ParsedDBCResponse,
    PropertyResultEntry,
    PropertyViolationResponse,
    Response,
    SuccessResponse,
    ValidationIssue,
    is_object_list,
    is_str_dict,
)
from ._helpers import normalize_dbc, validate_rational
from ._log import LogEvent, log_event
from ._types import ProtocolError

_logger = logging.getLogger("aletheia")


def validate_issue_severities(issues: list[ValidationIssue]) -> list[ValidationIssue]:
    """Validate issue severities and return the list unchanged, for chaining.

    The canonical wire values are ``"error"`` and ``"warning"`` — see
    ``Protocol/ResponseFormat.agda::formatIssueSeverity``. Anything else is a
    protocol violation and raises ``ProtocolError``.
    """
    for issue in issues:
        sev = issue.get("severity")
        if sev not in ("error", "warning"):
            raise ProtocolError(f"Unknown validation severity: {sev!r}")
    return issues


def build_error_response(response: Response) -> ErrorResponse:
    """Build an ``ErrorResponse`` from a raw FFI response dict.

    The Agda core always emits both ``code`` and ``message`` as strings
    on ``status = "error"``. Either field missing or non-string indicates
    a malformed response (FFI drift, hand-crafted test stub, or
    third-party tooling writing to the same queue) and is surfaced as a
    ``ProtocolError`` rather than being papered over with a default —
    the defaults (``""`` for Python, ``"Unknown error"`` for C++) used
    to diverge across bindings, and R16 shipped with a silent "unknown
    error code" regression in production logs.
    """
    code = response.get("code")
    if not isinstance(code, str):
        raise ProtocolError(
            "Error response missing or non-string 'code' field;"
            + f" got {type(code).__name__}"
        )
    message = response.get("message")
    if not isinstance(message, str):
        raise ProtocolError(
            "Error response missing or non-string 'message' field;"
            + f" got {type(message).__name__}"
        )
    return {"status": "error", "code": code, "message": message}


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

    raise ProtocolError(
        f"Unexpected response status: {status!r} (expected 'success' or 'error')"
    )


def parse_parsed_dbc_response(
    response: Response,
) -> ParsedDBCResponse | ErrorResponse:
    """Parse a response from parseDBC / parseDBCText.

    On success the Agda core emits ``ParsedDBCResponse`` carrying the
    canonical parsed body plus any non-error issues (warnings).  On
    failure it emits ``ErrorResponse`` with a typed code.
    """
    status = response.get("status")

    if status == "success":
        dbc_field = response.get("dbc")
        warnings_field = response.get("warnings", [])
        if not is_str_dict(dbc_field):
            raise ProtocolError(
                "parseDBC success response missing 'dbc' object"
            )
        if not is_object_list(warnings_field):
            raise ProtocolError(
                "parseDBC success response 'warnings' must be a list of objects"
            )
        warnings = cast(list[ValidationIssue], list(warnings_field))
        # Agda emits non-integer rationals on the wire as
        # ``{"numerator": n, "denominator": d}`` dicts; ``normalize_dbc``
        # converts those back to ``Fraction`` so callers see a real
        # ``DBCDefinition`` instead of a typed-cast lie. This is the
        # symmetry of ``FractionJSONEncoder`` on the request side, and
        # mirrors what Go's ``parseRational`` and the C++ JSON deserialiser
        # already do — the asymmetry was a Python-side bug surfaced by
        # B.3.f's switch to the Agda-backed ``dbc_to_json`` default.
        return {
            "status": "success",
            "dbc": normalize_dbc(dbc_field),
            "warnings": validate_issue_severities(warnings),
        }

    if status == "error":
        return build_error_response(response)

    raise ProtocolError(
        f"Unexpected response status: {status!r} (expected 'success' or 'error')"
    )


def parse_frame_response(
    response: Response,
) -> AckResponse | PropertyViolationResponse | ErrorResponse:
    """Parse a single frame response into a typed result."""
    status = response.get("status")

    if status == "ack":
        return {"status": "ack"}

    if status == "fails":
        prop_type = response.get("type")
        if prop_type != "property":
            raise ProtocolError(f"Expected type='property', got {prop_type}")
        prop_index = validate_rational("property_index", response.get("property_index"))
        ts_rational = validate_rational("timestamp", response.get("timestamp"))
        result_violation: PropertyViolationResponse = {
            "status": "fails",
            "type": "property",
            "property_index": prop_index,
            "timestamp": ts_rational,
        }
        reason = response.get("reason")
        if isinstance(reason, str):
            result_violation["reason"] = reason
        return result_violation

    if status == "error":
        return build_error_response(response)

    raise ProtocolError(
        f"Unexpected response status: {status!r} (expected 'ack', 'fails', or 'error')"
    )


def parse_event_response(
    response: Response, event_kind: str, timestamp: int,
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
        raise ProtocolError(f"Unknown event_kind {event_kind!r}")

    status = response.get("status")
    # Trace events (Error/Remote) always resolve to `Response.Ack` in Agda
    # (see Protocol/StreamState.agda handleTraceEvent), so the wire status is
    # always "ack". Tightened to match the Agda protocol exactly — Go
    # parseEventAck and C++ parse_event_ack enforce the same.
    if status == "ack":
        log_event(
            _logger, logging.DEBUG, event,
            ts=timestamp, response="ack",
        )
        return {"status": "ack"}
    if status == "error":
        result_error = build_error_response(response)
        log_event(
            _logger, logging.DEBUG, event,
            ts=timestamp, response="error", code=result_error["code"],
        )
        raise ProtocolError(
            f"{event_kind} failed: {result_error['message']}",
            code=result_error["code"],
        )
    raise ProtocolError(
        f"Unexpected {event_kind} response status: {status!r}"
        + " (expected 'ack' or 'error')"
    )


def parse_finalization_results(
    response: Response,
    enrich: Callable[[PropertyResultEntry], None],
) -> list[PropertyResultEntry]:
    """Parse end-of-stream property finalization results.

    ``enrich`` is invoked once per ``fails``/``unresolved`` entry so the
    client can attach an ``enrichment`` field (signals, formula_desc,
    enriched_reason, core_reason) using its own diagnostic and cache state.
    """
    results_raw = response.get("results")
    if not isinstance(results_raw, list):
        raise ProtocolError(
            "Missing or invalid 'results' in finalization response"
        )
    # Treat results as raw dicts for defensive parsing — the FFI
    # JSON is untrusted and may omit required keys.
    raw_results = cast(list[dict[str, object]], results_raw)
    entries: list[PropertyResultEntry] = []
    for raw in raw_results:
        entry_status = raw.get("status")
        if entry_status not in ("fails", "holds", "unresolved"):
            raise ProtocolError(
                f"Invalid 'status' in finalization result entry: {entry_status!r}"
            )
        raw_prop_index = raw.get("property_index")
        if raw_prop_index is None:
            raise ProtocolError(
                "Missing 'property_index' in finalization result entry"
            )
        prop_index = validate_rational("property_index", raw_prop_index)
        # entry_status is now narrowed to Literal["fails","holds","unresolved"]
        result_entry: PropertyResultEntry = {
            "type": "property",
            "status": entry_status,
            "property_index": prop_index,
        }
        if entry_status in ("fails", "unresolved"):
            ts = raw.get("timestamp")
            if ts is not None:
                result_entry["timestamp"] = validate_rational("timestamp", ts)
            reason = raw.get("reason")
            if isinstance(reason, str):
                result_entry["reason"] = reason
            enrich(result_entry)
        entries.append(result_entry)
    return entries
