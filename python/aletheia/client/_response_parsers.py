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
from aletheia.client._types import DBCValidationFailedError, ProtocolError
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
    """Validate issue severities and return the list unchanged, for chaining.

    The canonical wire values are ``"error"`` and ``"warning"`` — see
    ``Protocol/ResponseFormat.agda::formatIssueSeverity``. Anything else is a
    protocol violation and raises ``ProtocolError``.
    """
    for issue in issues:
        sev = issue.get("severity")
        if sev not in ("error", "warning"):
            msg = f"Unknown validation severity: {sev!r}"
            raise ProtocolError(msg)
    return issues


def _extract_bound_triple(response: Response) -> tuple[str, int, int] | None:
    """Return the ``(bound_kind, observed, limit)`` triple, or ``None`` if absent.

    All-or-nothing: a partial triple is treated as missing, matching the C++
    binding's degrade-to-nullopt rule in ``make_json_error``. ``bool`` is
    excluded because ``isinstance(True, int)`` is ``True`` and a boolean
    observed/limit is a malformed wire value, not a count. Single source for
    the triple shape, shared by :func:`build_error_response` (which folds it
    into the ``ErrorResponse``) and :func:`lift_input_bound_exceeded` (which
    gates it on the wire code) — no call site re-derives the field rules.
    """
    bound_kind = response.get("bound_kind")
    observed = response.get("observed")
    limit = response.get("limit")
    if (
        isinstance(bound_kind, str)
        and isinstance(observed, int)
        and not isinstance(observed, bool)
        and isinstance(limit, int)
        and not isinstance(limit, bool)
    ):
        return (bound_kind, observed, limit)
    return None


def lift_input_bound_exceeded(response: Response) -> tuple[str, int, int] | None:
    """Extract the bound triple from an ``input_bound_exceeded`` error, else None.

    Gates on the wire code — like :func:`lift_validation_issues` and the
    Go / C++ / Rust decoders — then reuses :func:`_extract_bound_triple`. The
    single rule for the code→triple lift so no call site re-implements it: the
    client's ``validate_dbc`` raises :class:`InputBoundExceededError` from the
    returned triple, and the load routes' bound rejects flow through the same
    wire code. A bound-coded error whose triple is missing/partial degrades to
    ``None`` (falls through to the generic error path) rather than raising with
    fabricated fields.
    """
    if response.get("code") != "input_bound_exceeded":
        return None
    return _extract_bound_triple(response)


def lift_validation_issues(
    response: Response,
) -> tuple[list[ValidationIssue], bool] | None:
    """Extract the ``issues`` / ``has_errors`` pair from an error envelope.

    Validation-failure errors (``code == "handler_validation_failed"`` from
    ``parseDBC`` / ``parseDBCText``) append the ``validation``-response
    issue list plus ``has_errors`` via ``Protocol/ResponseFormat.
    errorExtras``.  Both fields must be present and well-typed — every
    issue an object with string ``code`` / ``detail`` and a canonical
    severity — else the payload is treated as missing rather than partial
    (the degrade rule of the ``bound_kind`` / ``observed`` / ``limit``
    triple in :func:`build_error_response`).
    """
    # Gate on the wire code, like the Go / C++ / Rust decoders: another
    # error envelope that happens to carry has_errors/issues-shaped keys
    # must not be mis-lifted into validation issues.
    if response.get("code") != "handler_validation_failed":
        return None
    has_errors = response.get("has_errors")
    raw_issues = response.get("issues")
    if not isinstance(has_errors, bool) or not is_object_list(raw_issues):
        return None
    if not all(
        is_str_dict(item)
        and isinstance(item.get("code"), str)
        and isinstance(item.get("detail"), str)
        for item in raw_issues
    ):
        return None
    issues = cast("list[ValidationIssue]", list(raw_issues))
    try:
        return validate_issue_severities(issues), has_errors
    except ProtocolError:
        return None


def raise_if_dbc_validation_failed(response: Response, msg: str) -> None:
    """Raise :class:`DBCValidationFailedError` for a structured DBC validation failure.

    Returns normally when ``response`` is not a structured validation failure, so
    the caller raises its own fallback (``ProtocolError`` on the client,
    ``ValidationError`` in the converter). The single lift-and-raise shared by the
    client's DBC routes and the ``dbc`` converter — one wire-code gate, no
    per-caller re-implementation.
    """
    lifted = lift_validation_issues(response)
    if lifted is not None:
        issues, has_errors = lifted
        raise DBCValidationFailedError(
            msg, issues, has_errors=has_errors, code="handler_validation_failed"
        )


def build_error_response(response: Response) -> ErrorResponse:
    """Build an ``ErrorResponse`` from a raw FFI response dict.

    The Agda core always emits both ``code`` and ``message`` as strings
    on ``status = "error"``. Either field missing or non-string indicates
    a malformed response (FFI drift, hand-crafted test stub, or
    third-party tooling writing to the same queue) and is surfaced as a
    ``ProtocolError`` rather than being papered over with a default —
    the defaults (``""`` for Python, ``"Unknown error"`` for C++) used
    to diverge across bindings and produced a silent "unknown error
    code" regression in production logs.

    InputBoundExceeded errors carry an additional ``bound_kind`` /
    ``observed`` / ``limit`` triple via ``Protocol/ResponseFormat.
    errorExtras``; all three must be present and well-typed when any
    one is, else the payload is treated as missing rather than partial
    (matches the C++ binding's degrade-to-nullopt rule in
    ``make_json_error``).

    Validation-failure errors carry the ``issues`` / ``has_errors`` pair
    under the same all-or-nothing rule (see
    :func:`lift_validation_issues`).
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
    triple = _extract_bound_triple(response)
    if triple is not None:
        out["bound_kind"], out["observed"], out["limit"] = triple
    lifted = lift_validation_issues(response)
    if lifted is not None:
        out["issues"], out["has_errors"] = lifted
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
    failure it emits ``ErrorResponse`` with a typed code.
    """
    status = response.get("status")

    if status == "success":
        dbc_field = response.get("dbc")
        warnings_field = response.get("warnings", [])
        if not is_str_dict(dbc_field):
            msg = "parseDBC success response missing 'dbc' object"
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
    `"property_batch"`; the `results` list holds one or more
    `PropertyResultEntry` objects (fails / holds / unresolved).  A
    no-event frame still returns `AckResponse` ({"status": "ack"});
    the batch is never empty when present.
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
        if not isinstance(raw_results, list):
            msg = "property_batch response missing 'results' array"
            raise ProtocolError(msg)
        if not raw_results:
            msg = (
                "property_batch response 'results' must be non-empty"
                " (zero-event frames are encoded as ack)"
            )
            raise ProtocolError(msg)
        parsed_results: list[PropertyResultEntry] = []
        for raw_item in raw_results:  # type: ignore[reportUnknownVariableType]
            if not isinstance(raw_item, dict):
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
    """
    inner_type = raw.get("type")
    if inner_type != "property":
        msg = f"property_batch event has unexpected type={inner_type!r} (expected 'property')"
        raise ProtocolError(msg)
    inner_status = raw.get("status")
    if inner_status not in ("fails", "holds", "unresolved"):
        msg = (
            f"property_batch event has unexpected status={inner_status!r}"
            " (expected 'fails', 'holds', or 'unresolved')"
        )
        raise ProtocolError(msg)
    prop_index = validate_integer_field("property_index", raw.get("property_index"))
    entry: PropertyResultEntry = {
        "type": "property",
        "status": inner_status,
        "property_index": prop_index,
    }
    if inner_status == "fails":
        entry["timestamp"] = validate_integer_field("timestamp", raw.get("timestamp"))
    reason = raw.get("reason")
    if isinstance(reason, str):
        entry["reason"] = reason
    return entry


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
        msg = f"{event_kind} failed: {result_error['message']}"
        raise ProtocolError(msg, code=result_error["code"])
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
    """
    results_raw = response.get("results")
    if not isinstance(results_raw, list):
        msg = "Missing or invalid 'results' in finalization response"
        raise ProtocolError(msg)
    # Treat results as raw dicts for defensive parsing — the FFI
    # JSON is untrusted and may omit required keys.
    raw_results = cast("list[dict[str, object]]", results_raw)
    entries: list[PropertyResultEntry] = []
    for raw in raw_results:
        entry_status = raw.get("status")
        if entry_status not in ("fails", "holds", "unresolved"):
            msg = f"Invalid 'status' in finalization result entry: {entry_status!r}"
            raise ProtocolError(msg)
        raw_prop_index = raw.get("property_index")
        if raw_prop_index is None:
            msg = "Missing 'property_index' in finalization result entry"
            raise ProtocolError(msg)
        prop_index = validate_integer_field("property_index", raw_prop_index)
        # entry_status is now narrowed to Literal["fails","holds","unresolved"]
        result_entry: PropertyResultEntry = {
            "type": "property",
            "status": entry_status,
            "property_index": prop_index,
        }
        if entry_status in ("fails", "unresolved"):
            ts = raw.get("timestamp")
            if ts is not None:
                result_entry["timestamp"] = validate_integer_field("timestamp", ts)
            reason = raw.get("reason")
            if isinstance(reason, str):
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
    ``item.(map[string]any)`` check raise on the same inputs. A missing
    ``property_index`` is a protocol violation and is rejected rather than
    silently defaulted.
    """
    raw_warnings = response.get("warnings", [])
    if not is_object_list(raw_warnings):
        msg = "'warnings' must be a list in end-of-stream complete response"
        raise ProtocolError(msg)
    warnings: list[CompleteWarning] = []
    for raw in raw_warnings:
        if not is_str_dict(raw):
            msg = "end-of-stream warning entry must be an object"
            raise ProtocolError(msg)
        raw_prop_index = raw.get("property_index")
        if raw_prop_index is None:
            msg = "Missing 'property_index' in end-of-stream warning entry"
            raise ProtocolError(msg)
        warnings.append(
            {
                "kind": cast("str", raw.get("kind", "")),
                "property_index": validate_integer_field("property_index", raw_prop_index),
                "detail": cast("str", raw.get("detail", "")),
            }
        )
    return warnings
