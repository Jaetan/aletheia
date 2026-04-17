"""Structured logging schema for the Python binding.

Mirrors the 15-event vocabulary used by the Go binding's ``slog`` calls and
the C++ binding's custom ``Logger`` class so a downstream log collector can
treat all three bindings interchangeably.  The set is the authoritative
source of truth — adding a new event here forces the call site to pick a
known name, and the logging tests (``tests/test_logging.py``) assert that
every record emitted by the client carries a value from ``LogEvent``.

Design choices:

* ``str, Enum`` (i.e. ``StrEnum``) so the enum value is the literal log
  message text (``LogEvent.DBC_PARSED`` prints as ``"dbc.parsed"``) and
  ``msg=`` slots in with no extra formatting.
* ``log_event`` fills an ``extra`` dict with the event name plus
  caller-supplied keyword fields.  The fields are forwarded as distinct
  ``LogRecord`` attributes, so structured handlers (``JSONFormatter``,
  ``pythonjsonlogger``, an OpenTelemetry bridge) can parse them directly.
* Human-readable fallback: ``fmt`` still renders ``event.name key=val ...``
  so the default ``StreamHandler`` output stays grep-friendly and every
  existing log-scraping regex keeps matching.

Do NOT invent new event names in call sites — add the name here first,
then use ``log_event(logger, LogEvent.NEW_NAME, ...)``.
"""

import logging
from enum import Enum
from typing import Final


class LogEvent(str, Enum):
    """Structured log event names shared with Go (``slog``) and C++ (``Logger``).

    Exactly 15 values — the set must stay identical across bindings.  Every
    ``Client``/``AletheiaClient`` observability call site uses one of these;
    any new event must be added here first.
    """

    # --- Lifecycle (INFO) ---
    DBC_PARSED = "dbc.parsed"
    PROPERTIES_SET = "properties.set"
    STREAM_STARTED = "stream.started"
    STREAM_ENDED = "stream.ended"

    # --- Frame processing (DEBUG) ---
    FRAME_PROCESSED = "frame.processed"
    ERROR_EVENT_SENT = "error_event.sent"
    REMOTE_EVENT_SENT = "remote_event.sent"

    # --- Enrichment diagnostics (WARNING) ---
    ENRICHMENT_PROPERTY_INDEX_OOB = "enrichment.property_index_oob"
    ENRICHMENT_EXTRACTION_FAILED = "enrichment.extraction_failed"

    # --- Extraction cache (DEBUG / WARNING) ---
    CACHE_HIT = "cache.hit"
    CACHE_MISS = "cache.miss"
    CACHE_FULL = "cache.full"

    # --- Extraction errors (WARNING) ---
    EXTRACTION_PROCESS_FAILED = "extraction.process_failed"
    EXTRACTION_PARSE_FAILED = "extraction.parse_failed"

    # --- Backend diagnostics (WARNING) ---
    RTS_CORES_MISMATCH = "rts.cores_mismatch"


# Exposed as ``Final[frozenset[str]]`` so the test suite can assert that
# every captured ``LogRecord.msg`` (or ``extra["event"]``) is a member.
KNOWN_EVENTS: Final[frozenset[str]] = frozenset(e.value for e in LogEvent)


def _format_fields(fields: dict[str, object]) -> str:
    """Render kwargs as ``key=value`` pairs in insertion order."""
    return " ".join(f"{k}={v}" for k, v in fields.items())


def log_event(
    logger: logging.Logger,
    level: int,
    event: LogEvent,
    /,
    **fields: object,
) -> None:
    """Emit a structured log record with event name + key/value fields.

    The human-readable message is ``"event.name key=val ..."`` so the default
    ``StreamHandler`` output is still greppable.  In addition, every field
    is attached as a distinct attribute on the ``LogRecord`` via ``extra``
    (with the event name itself under the reserved ``event`` key), so
    structured handlers see them as first-class data.

    Args:
        logger:  The target ``logging.Logger`` (usually module-local).
        level:   A standard ``logging`` level (``logging.INFO`` etc.).
        event:   A member of :class:`LogEvent` — the event name.
        **fields: Key/value pairs to attach to the record.
    """
    # Short-circuit before any allocation when the target level is disabled
    # (the default at DEBUG on the streaming hot path). Mirrors the stdlib
    # ``Logger.debug``/``info`` fast path: without this guard a no-handler
    # DEBUG call still built the ``extra`` dict, formatted the message, and
    # walked ``Logger.log`` — a measurable regression on Stream LTL.
    if not logger.isEnabledFor(level):
        return
    # ``event`` is the canonical key structured collectors look for; match
    # Go's ``slog`` attribute name so cross-binding log pipelines can parse
    # both streams with the same code.
    extra: dict[str, object] = {"event": event.value, **fields}
    if fields:
        msg = f"{event.value} {_format_fields(fields)}"
    else:
        msg = event.value
    logger.log(level, msg, extra=extra)
