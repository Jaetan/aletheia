# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Grep-guard for test files that reach into ``aletheia.client._*`` internals.

Test modules are allowed to exercise implementation detail directly, but
each such import path is enumerated here so that a new reach-through
into a ``_``-prefixed module produces an explicit promote-or-justify
decision in the review round that added it — rather than silently
accumulating an undeclared private-API surface area.

How to extend:
    1. If the internal symbol has grown into genuine public API, promote
       it to the top-level ``aletheia`` package (the single canonical
       public surface) in the same commit.
    2. If it must stay private, add the (test_file, module, symbol)
       triple to ``_ALLOWED`` with a one-line justification above it.
"""

import ast
from pathlib import Path

import aletheia.client

_TESTS_DIR = Path(__file__).parent

# (test_file_basename, private_module, symbol) triples. Each symbol is a
# concrete reach-through that has been consciously accepted.
_ALLOWED: frozenset[tuple[str, str, str]] = frozenset(
    {
        # Structured-logging internals — per-event string catalogue is
        # implementation detail of Client.log_event; a drift test needs to
        # see the raw mapping to compare against the 15 wire events.
        ("test_logging.py", "aletheia.client._log", "KNOWN_EVENTS"),
        ("test_logging.py", "aletheia.client._log", "LogEvent"),
        # Cross-binding YAML parity gate — anchors the LogEvent enum to
        # docs/LOG_EVENTS.yaml (the SSOT shared with Go/C++). Same internal-
        # vocabulary justification as test_logging.py above.
        ("test_log_events_parity.py", "aletheia.client._log", "KNOWN_EVENTS"),
        ("test_log_events_parity.py", "aletheia.client._log", "LogEvent"),
        # Binary extraction buffer parser — exercised structurally to lock
        # the on-wire layout. If the parser grows stable consumers outside
        # the test suite, promote the symbols then.
        (
            "test_binary_extraction.py",
            "aletheia.client._client_bin",
            "EXTRACTION_ERROR_MESSAGES",
        ),
        (
            "test_binary_extraction.py",
            "aletheia.client._client_bin",
            "EXTRACTION_ERROR_MESSAGES_BY_CODE",
        ),
        (
            "test_binary_extraction.py",
            "aletheia.client._client_bin",
            "ExtractionErrorCode",
        ),
        (
            "test_binary_extraction.py",
            "aletheia.client._client_bin",
            "parse_extraction_buffer",
        ),
        # Rational-helper conversions — kept internal because the public
        # API takes ``Fraction`` directly; the helpers convert user-supplied
        # floats/strings for the loader paths and don't need to be called
        # from user code.
        # PY-D-16.1 (R23): _helpers.py split into a package; the test paths
        # below pin to the new submodule layout.
        (
            "test_types_and_conditions.py",
            "aletheia.client._helpers.rational",
            "float_to_rational",
        ),
        (
            "test_types_and_conditions.py",
            "aletheia.client._helpers.rational",
            "parse_rational",
        ),
        (
            "test_property_hypothesis.py",
            "aletheia.client._helpers.rational",
            "parse_rational",
        ),
        (
            "test_types_and_conditions.py",
            "aletheia.client._types",
            "validate_can_id",
        ),
        # DLC-to-bytes table is an internal encoding detail of the frame
        # builder; the test exercises the mapping directly to lock the
        # CAN-FD 9-15 code points. Not public API — user code goes through
        # ``AletheiaClient.send_frame``/``data_frame``.
        (
            "test_types_and_conditions.py",
            "aletheia.client._types",
            "bytes_to_dlc",
        ),
        (
            "test_types_and_conditions.py",
            "aletheia.client._types",
            "dlc_to_bytes",
        ),
        # Event-response parser — Client.log_event handler already covers
        # the happy path; this guards the error-response decoding branches
        # in isolation.
        (
            "test_unified_client_events_rts.py",
            "aletheia.client._response_parsers",
            "parse_event_response",
        ),
        # ``dump_json`` was promoted to ``aletheia.protocols`` in R23 PY-D-16.2
        # so it's no longer a private-import; whitelist entry removed.
        # Strict-contract guard for the shared error-response builder —
        # exercised directly because the surface-level tests all go through
        # ``parse_frame_response`` / ``parse_event_response`` and only hit
        # the happy path; this catches malformed-dict regressions at the
        # helper level.
        (
            "test_response_parsers.py",
            "aletheia.client._response_parsers",
            "build_error_response",
        ),
        # ``FractionJSONEncoder`` was promoted to ``aletheia.protocols`` in
        # R23 PY-D-16.2 so it's no longer a private-import; whitelist entry
        # removed.
        # Enrichment helpers — pure functions used by the client to attach
        # ``enrichment`` metadata to violation results; kept internal because
        # they depend on ``_diags``/``_caches`` state that is client-owned.
        # Tested in isolation for per-helper semantics (signal extraction,
        # formula formatting, diagnostic assembly).
        (
            "test_enrichment.py",
            "aletheia.client._enrichment",
            "build_diagnostic",
        ),
        (
            "test_enrichment.py",
            "aletheia.client._enrichment",
            "collect_signals",
        ),
        (
            "test_enrichment.py",
            "aletheia.client._enrichment",
            "format_enriched_reason",
        ),
        (
            "test_enrichment.py",
            "aletheia.client._enrichment",
            "format_formula",
        ),
        # FFI loader security test (R19 cluster B / PY-B-26.11) exercises the
        # ALETHEIA_LIB world/group-writable rejection path directly.
        # ``find_ffi_library`` is binding-internal — public callers go
        # through ``AletheiaClient`` which calls the loader transitively; the
        # security check needs to be tested in isolation with monkeypatched
        # env vars and synthetic permission modes.
        ("test_ffi_loader_security.py", "aletheia.client._ffi", "find_ffi_library"),
        # CAN-FD BRS / ESI encoding helper (R19 Phase 2 cluster 18 —
        # AGDA-D-10.1).  ``encode_maybe_bool`` mirrors the Haskell shim's
        # ``mkMaybeBool`` and is exercised directly to lock the
        # (present, value) byte pair convention against the C ABI; user
        # code goes through ``send_frame(brs=…, esi=…)`` which calls this
        # transitively.
        ("test_canfd_brs_esi.py", "aletheia.client._types", "encode_maybe_bool"),
    }
)


def _collect_private_imports() -> list[tuple[str, str, str]]:
    """Return every ``from aletheia.client._X import Y`` in tests/."""
    found: list[tuple[str, str, str]] = []
    for test_file in _TESTS_DIR.glob("test_*.py"):
        source = test_file.read_text(encoding="utf-8")
        tree = ast.parse(source)
        for node in ast.walk(tree):
            if not isinstance(node, ast.ImportFrom):
                continue
            module = node.module or ""
            if not module.startswith("aletheia.client._"):
                continue
            found.extend((test_file.name, module, alias.name) for alias in node.names)
    return found


def test_private_imports_are_whitelisted() -> None:
    """Each reach-through into ``aletheia.client._*`` is declared."""
    actual = set(_collect_private_imports())
    undeclared = actual - _ALLOWED
    assert not undeclared, (
        "Test files import from ``aletheia.client._*`` private modules "
        + "without being declared in the whitelist:\n  "
        + "\n  ".join(f"{tf}: from {mod} import {sym}" for tf, mod, sym in sorted(undeclared))
        + "\n\nPromote the symbol to a public API path, or add the triple "
        + "to ``_ALLOWED`` in this test with a one-line justification."
    )


def test_whitelist_has_no_stale_entries() -> None:
    """Every whitelist entry corresponds to an actual import."""
    actual = set(_collect_private_imports())
    stale = _ALLOWED - actual
    assert not stale, (
        "Whitelist declares private imports that no test file uses any "
        + "more — remove them:\n  "
        + "\n  ".join(f"{tf}: from {mod} import {sym}" for tf, mod, sym in sorted(stale))
    )


def test_client_package_exposes_no_public_reexports() -> None:
    """``aletheia.client`` is internal — it must expose no public names.

    The top-level ``aletheia`` package is the single canonical public
    surface. A non-underscore name re-appearing on ``aletheia.client``
    (or an ``__all__`` declaration) would silently re-introduce the dual
    import path retired when the client sub-package was demoted to internal
    plumbing — defeating the goal that every client name has exactly one
    public import path.
    """
    public = sorted(name for name in vars(aletheia.client) if not name.startswith("_"))
    assert not public, (
        "aletheia.client must not expose public re-exports — import the client "
        + "surface from the top-level ``aletheia`` package instead. Found: "
        + ", ".join(public)
    )
    assert not hasattr(aletheia.client, "__all__"), (
        "aletheia.client must not declare ``__all__``: it is internal "
        + "implementation detail; the public surface lives in ``aletheia.__all__``."
    )
