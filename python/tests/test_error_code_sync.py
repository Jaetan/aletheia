"""Agda/Python ``ErrorCode`` enum synchronization.

Guards the Python ``ErrorCode`` enum in ``aletheia.protocols`` against
drift from Agda's ``errorCode``/``parseErrorCode``/``frameErrorCode``/
etc. families in ``src/Aletheia/Error.agda``.  The Agda source is the
authoritative manifest; this test parses each of the six ``*ErrorCode``
functions, collects every literal string they emit, and asserts that
the Python enum is a superset (every Agda wire value has a Python
member) AND a subset (every Python member has an Agda emission site).

Rationale: the binding-layer ``ErrorCode`` enum is the cross-binding
machine-readable contract (Go and C++ have parallel enums that must
stay identical).  Without this reciprocal test, an Agda addition
silently yields ``"Unknown error code"`` in production because all
three bindings coerce unknown strings back to a generic fallback.
"""

import re
from pathlib import Path

import pytest

from aletheia.protocols import ErrorCode


_AGDA_FILE = (
    Path(__file__).resolve().parents[2] / "src" / "Aletheia" / "Error.agda"
)
_AGDA_FILE_MISSING = not _AGDA_FILE.exists()
_SKIP_REASON = (
    f"Agda source required for ErrorCode drift test but not at {_AGDA_FILE}"
    " — skip from installed-wheel test runs; ``pytest.fail`` stays for"
    " structural parse failures."
)

# The six ``*ErrorCode`` function families ``errorCode`` dispatches through.
# Each family emits a string literal on the RHS of ``= "..."``; collecting
# those literals across all six yields the canonical wire-value set.
_ERROR_CODE_FUNCTIONS: tuple[str, ...] = (
    "parseErrorCode",
    "frameErrorCode",
    "extractionErrorCode",
    "routeErrorCode",
    "handlerErrorCode",
    "dispatchErrorCode",
)

# Lines like:     parseErrorCode (MissingField _)           = "parse_missing_field"
_RHS_STRING_RE = re.compile(r'=\s*"([^"\n]+)"\s*$')


def _collect_agda_error_codes() -> set[str]:
    """Read every literal emitted by the Agda ``*ErrorCode`` families."""
    text = _AGDA_FILE.read_text(encoding="utf-8")
    # Recursive/wrapper cases (``parseErrorCode (InContext _ inner) = parseErrorCode
    # inner``) don't match _RHS_STRING_RE because the RHS is not a string
    # literal — they delegate and are therefore correctly skipped.
    codes: set[str] = set()
    for line in text.splitlines():
        stripped = line.lstrip()
        if not any(stripped.startswith(fn + " ") for fn in _ERROR_CODE_FUNCTIONS):
            continue
        match = _RHS_STRING_RE.search(line)
        if match:
            codes.add(match.group(1))
    return codes


@pytest.mark.skipif(_AGDA_FILE_MISSING, reason=_SKIP_REASON)
class TestErrorCodeSync:
    """Python ``ErrorCode`` mirrors Agda's wire-value string set."""

    def test_agda_codes_parsed(self) -> None:
        """The Agda parser found *some* codes — fails fast on a broken regex."""
        agda_codes = _collect_agda_error_codes()
        assert agda_codes, "parsed zero codes — the regex or Agda layout changed"
        # Smoke-check one well-known value from each family.
        assert "parse_missing_field" in agda_codes
        assert "frame_signal_not_found" in agda_codes
        assert "extraction_mux_value_mismatch" in agda_codes
        assert "route_unknown_command" in agda_codes
        assert "handler_no_dbc" in agda_codes
        assert "dispatch_missing_type_field" in agda_codes

    def test_every_agda_code_is_in_python_enum(self) -> None:
        """Adding an Agda error constructor forces a Python enum update."""
        agda_codes = _collect_agda_error_codes()
        python_codes = {member.value for member in ErrorCode}
        missing_in_python = agda_codes - python_codes
        assert not missing_in_python, (
            f"Agda emits error codes that have no Python ErrorCode member: "
            f"{sorted(missing_in_python)}.  Add them to "
            f"``aletheia/protocols.py::ErrorCode`` (and mirror in Go/C++)."
        )

    def test_every_python_code_is_in_agda(self) -> None:
        """Python does not claim codes Agda never emits — prevents stale members."""
        agda_codes = _collect_agda_error_codes()
        python_codes = {member.value for member in ErrorCode}
        unused_in_python = python_codes - agda_codes
        assert not unused_in_python, (
            f"Python ErrorCode declares values Agda never emits: "
            f"{sorted(unused_in_python)}.  Either remove from the enum "
            f"or add the matching ``*ErrorCode`` clause in Error.agda."
        )
