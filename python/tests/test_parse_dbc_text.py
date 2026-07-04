# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
"""Track B.3.e smoke tests for the ``parse_dbc_text`` JSON command.

The Agda text parser (verified in Track B.3.d) is exposed via a new JSON
command that composes ``parseText`` with the runtime validator and emits
``ParsedDBCResponse`` on success or ``ErrorResponse`` on parse / validation
failure.  These tests hit the real FFI-backed client (no mocks) so the
entire stack — Routing → Handlers → parseText → validateDBCFull → JSON —
is exercised end-to-end.
"""

from __future__ import annotations

from pathlib import Path

from aletheia import AletheiaClient
from aletheia.types import DLCCode

CORPUS_DIR = Path(__file__).parent / "fixtures" / "dbc_corpus"


def _read_corpus(name: str) -> str:
    return (CORPUS_DIR / name).read_text(encoding="utf-8")


class TestParseDBCTextSuccess:
    """Happy path: well-formed DBC text → status=success + dbc + warnings."""

    def test_minimal_dbc_parses(self) -> None:
        """A well-formed DBC text returns success with the parsed body."""
        text = _read_corpus("minimal.dbc")
        with AletheiaClient() as client:
            resp = client.parse_dbc_text(text)
        assert resp["status"] == "success"
        assert "dbc" in resp
        assert "warnings" in resp
        # minimal.dbc declares 2 messages (EngineStatus, BrakeStatus)
        assert len(resp["dbc"]["messages"]) == 2
        names = {m["name"] for m in resp["dbc"]["messages"]}
        assert names == {"EngineStatus", "BrakeStatus"}

    def test_parses_populates_signal_lookup(self) -> None:
        """After parse_dbc_text, signal extraction must be available."""
        text = _read_corpus("minimal.dbc")
        with AletheiaClient() as client:
            resp = client.parse_dbc_text(text)
            assert resp["status"] == "success"
            # 8 zero bytes — extraction should resolve every signal in EngineStatus.
            result = client.extract_signals(can_id=256, dlc=DLCCode(8), data=b"\x00" * 8)
        assert "EngineSpeed" in result.values
        assert "EngineTemp" in result.values
        # CoolantLevel has Vector__XXX → stripped to [] receivers, but the
        # signal itself is still present and extractable.
        assert "CoolantLevel" in result.values

    def test_warnings_field_present_even_when_empty(self) -> None:
        """The warnings field is always present, even when no warnings fire."""
        text = _read_corpus("minimal.dbc")
        with AletheiaClient() as client:
            resp = client.parse_dbc_text(text)
        assert resp["status"] == "success"
        # warnings is always a list, possibly empty
        assert isinstance(resp["warnings"], list)


class TestParseDBCTextFailure:
    """Failure paths: parse errors and validation errors are typed."""

    def test_garbage_input_returns_parse_error(self) -> None:
        """Non-DBC text returns a typed dbc_text_* parse error code."""
        with AletheiaClient() as client:
            resp = client.parse_dbc_text("this is not a DBC file at all")
        assert resp["status"] == "error"
        # Typed code from the Agda DBCTextParseError ADT.
        assert resp["code"].startswith("dbc_text_")

    def test_empty_input_returns_parse_error(self) -> None:
        """Empty input is rejected as a parse error."""
        with AletheiaClient() as client:
            resp = client.parse_dbc_text("")
        assert resp["status"] == "error"

    def test_validation_failure_carries_structured_issues(self) -> None:
        """A ``handler_validation_failed`` envelope decodes issues + has_errors.

        The issue list reuses the exact element shape of the ``validation``
        response; ``has_errors`` is the decoded wire value, not assumed.
        """
        text = _read_corpus("minimal.dbc").replace(" SG_ EngineTemp ", " SG_ EngineSpeed ")
        with AletheiaClient() as client:
            resp = client.parse_dbc_text(text)
        assert resp["status"] == "error"
        assert resp["code"] == "handler_validation_failed"
        assert resp.get("has_errors") is True
        issues = resp.get("issues")
        assert issues is not None
        assert "duplicate_signal_name" in {issue["code"] for issue in issues}

    def test_zero_length_le_signal_rejected_at_parse(self) -> None:
        """LE bitLength=0 surfaces as a parse error.

        The text parser's `buildSignal` rejects `1 ≤ᵇ bl ≡ false`; the
        `nothing` propagates through buildAllRaw → resolveSignalList →
        buildMessage (parser `fail`) and surfaces at the top level as
        a DBCTextParseError.  The wire code is `dbc_text_*` (the
        text-parser error vocabulary is intentionally coarser than the
        JSON parser's typed `parse_signal_bit_length_zero`).

        Tests both `length=1` (success) and `length=0` (error) on the
        same DBC template so bl=0 is the only differentiator — without
        the success case, any incidental parse failure (empty NS_/BS_,
        receiver-list shape, etc.) would silently satisfy the error
        assertion without exercising the new gate.
        """

        def _text(length: int) -> str:
            return (
                'VERSION ""\n'
                "\n"
                "NS_ :\n"
                "\n"
                "BS_:\n"
                "\n"
                "BU_: Engine\n"
                "\n"
                "BO_ 100 Msg: 1 Engine\n"
                f' SG_ SigLE : 0|{length}@1+ (1,0) [0|0] "" Engine\n'
            )

        with AletheiaClient() as client:
            ok = client.parse_dbc_text(_text(1))
            assert ok["status"] == "success", ok
            bad = client.parse_dbc_text(_text(0))
            assert bad["status"] == "error"
            assert bad["code"].startswith("dbc_text_")
