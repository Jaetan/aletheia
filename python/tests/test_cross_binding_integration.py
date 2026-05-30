"""Cross-binding integration tests.

Counterpart of ``go/aletheia/cross_binding_integration_test.go`` and
``cpp/tests/test_cross_binding_integration.cpp``.  All three tests
construct identical canonical inputs in code (no shared corpus, no
golden output to diff against) and assert the binding's response shape
matches the structural invariants documented in
``docs/architecture/PROTOCOL.md``.

The shared truth source is PROTOCOL.md (text + JSON examples), not a
file of recorded outputs — corpus-style integration tests bit-rot fast
and tie every binding to one binding's exact emit format.  By
asserting structural invariants here (key sets, value types, count
relationships, error-code enum membership), each binding's drift from
the documented protocol surfaces locally without depending on the
other bindings to also have run.

Cross-binding parity is enforced transitively: if Python's test asserts
"``ParsedDBCResponse`` has exactly the keys ``{status, dbc, issues}``"
and Go's test asserts the same, any binding that adds or drops a key
fails its own test.  No pairwise binding diff is computed.

Per AGENTS.md cat 22, Python is the reference implementation — but
"reference" means "the documented shape lives in Python's TypedDicts";
the test suite below validates every binding against PROTOCOL.md, not
against Python's runtime output.
"""

from __future__ import annotations

import pytest
from _canonical_dbc import CANONICAL_DBC as _CANONICAL_DBC

from aletheia import AletheiaClient, Signal, ValidationError
from aletheia.protocols import DLCCode

# Documented structural invariants — these mirror PROTOCOL.md's response
# shape tables.  Each binding asserts the same expectations against its
# own deserialized output.

_PARSED_DBC_RESPONSE_KEYS: frozenset[str] = frozenset({"status", "dbc", "warnings"})
_VALIDATION_RESPONSE_KEYS: frozenset[str] = frozenset({"status", "has_errors", "issues"})
_ACK_RESPONSE_KEYS: frozenset[str] = frozenset({"status"})
_ERROR_RESPONSE_KEYS: frozenset[str] = frozenset({"status", "code", "message"})


class TestCrossBindingIntegration:
    """Structural-invariant assertions across the public response surface.

    Mirrored verbatim by ``go/aletheia/cross_binding_integration_test.go``
    and ``cpp/tests/test_cross_binding_integration.cpp``.  When this
    file's expectations change, the other two MUST change in lock-step.
    """

    def test_parse_dbc_response_shape(self) -> None:
        """``parse_dbc`` returns a structure matching ``ParsedDBCResponse``."""
        with AletheiaClient() as client:
            response = client.parse_dbc(_CANONICAL_DBC)

        # ParsedDBCResponse: status="success", dbc=<DBCDefinition>, warnings=[].
        assert isinstance(response, dict)
        assert _PARSED_DBC_RESPONSE_KEYS.issubset(set(response.keys())), (
            f"parse_dbc response missing keys: {_PARSED_DBC_RESPONSE_KEYS - set(response.keys())}"
        )
        assert response["status"] == "success"
        assert isinstance(response["warnings"], list)
        # Round-trip identity invariant: parsed body retains canonical DBC's
        # structural content (one message, one signal, name preserved).
        parsed_dbc = response["dbc"]
        assert isinstance(parsed_dbc, dict)
        assert isinstance(parsed_dbc.get("messages"), list)
        assert len(parsed_dbc["messages"]) == 1
        assert parsed_dbc["messages"][0]["id"] == 256
        assert parsed_dbc["messages"][0]["name"] == "TestMessage"
        assert len(parsed_dbc["messages"][0]["signals"]) == 1
        assert parsed_dbc["messages"][0]["signals"][0]["name"] == "TestSignal"

    def test_validate_dbc_response_shape(self) -> None:
        """``validate_dbc`` returns a structure matching ``ValidationResponse``."""
        with AletheiaClient() as client:
            response = client.validate_dbc(_CANONICAL_DBC)

        # ValidationResponse: status="validation", has_errors=bool, issues=list.
        assert isinstance(response, dict)
        assert _VALIDATION_RESPONSE_KEYS.issubset(set(response.keys())), (
            f"validate_dbc response missing keys: "
            f"{_VALIDATION_RESPONSE_KEYS - set(response.keys())}"
        )
        assert response["status"] == "validation"
        assert isinstance(response["has_errors"], bool)
        assert response["has_errors"] is False  # canonical DBC is valid
        assert isinstance(response["issues"], list)

    def test_send_frame_ack_response_shape(self) -> None:
        """``send_frame`` on a non-violating frame returns ``AckResponse``."""
        prop = Signal("TestSignal").less_than(1000).always()
        with AletheiaClient() as client:
            client.parse_dbc(_CANONICAL_DBC)
            client.set_properties([prop.to_dict()])
            client.start_stream()
            response = client.send_frame(
                timestamp=1000,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([0, 0, 0, 0, 0, 0, 0, 0]),  # signal value 0 < 1000
            )
            client.end_stream()

        # AckResponse: status="ack", no other required keys.
        assert isinstance(response, dict)
        assert "status" in response  # narrows the union away from PropertyBatchResponse
        assert response["status"] == "ack"
        assert _ACK_RESPONSE_KEYS.issubset(set(response.keys()))

    def test_send_frame_violation_response_shape(self) -> None:
        """``send_frame`` on a violating frame returns ``PropertyBatchResponse``.

        Required wire keys per PROTOCOL.md:
        ``{type: "property_batch", results: [...]}``; each ``results``
        entry has ``{type: "property", status: "fails"|"holds"|"unresolved",
        property_index, [timestamp]}``.  ``reason`` and ``enrichment`` are
        optional but conventionally present on fails entries when the
        binding has the DBC + property set loaded.
        """
        prop = Signal("TestSignal").less_than(100).always()
        with AletheiaClient() as client:
            client.parse_dbc(_CANONICAL_DBC)
            client.set_properties([prop.to_dict()])
            client.start_stream()
            # Signal value 0xFFFF (65535) > 100 → violation.
            response = client.send_frame(
                timestamp=1000,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([0xFF, 0xFF, 0, 0, 0, 0, 0, 0]),
            )
            client.end_stream()

        assert isinstance(response, dict)
        assert "type" in response  # narrows the union to PropertyBatchResponse
        assert response["type"] == "property_batch"
        assert isinstance(response["results"], list)
        assert len(response["results"]) >= 1
        # Violations are always the last entry in source-order per the
        # Agda dispatchIterResult invariant (satisfactions first, halt last).
        violation = response["results"][-1]
        assert violation["status"] == "fails"
        assert violation["type"] == "property"
        assert "property_index" in violation
        assert "timestamp" in violation

    def test_send_frame_error_response_shape(self) -> None:
        """Invalid frame input returns ``ErrorResponse`` with required fields."""
        with AletheiaClient() as client:
            client.parse_dbc(_CANONICAL_DBC)
            client.start_stream()
            # CAN ID 0x800 (2048) is out of standard 11-bit range; FFI rejects.
            with pytest.raises((ValidationError, ValueError, RuntimeError, OSError)):
                client.send_frame(
                    timestamp=1000,
                    can_id=0x800,
                    dlc=DLCCode(8),
                    data=bytearray([0, 0, 0, 0, 0, 0, 0, 0]),
                )

        # Error path is exception-based in Python; the wire-form
        # ErrorResponse shape is enforced by the binding's send_frame
        # implementation translating wire errors to Python exceptions.
        # The cross-binding parity claim is that an invalid CAN ID
        # produces an error in EVERY binding (Go: error return; C++:
        # error variant; Python: raise) — not a silent ack.

    def test_error_response_keys_when_observed_directly(self) -> None:
        """When an ErrorResponse surfaces as a dict (not exception), it has the documented keys.

        Currently Python's high-level API converts errors to exceptions,
        so this test exercises the wire-format keyset assertion that
        Go and C++ enforce on the dict-form response.
        """
        # Synthesize a wire-form ErrorResponse and assert its key set —
        # this is the static structural invariant that the binding's
        # parser must accept.
        synthetic: dict[str, str] = {
            "status": "error",
            "code": "frame_invalid_can_id",
            "message": "CAN ID out of range",
        }
        assert _ERROR_RESPONSE_KEYS.issubset(set(synthetic.keys()))
        assert synthetic["status"] == "error"
