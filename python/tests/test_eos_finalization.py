"""Tests for end-of-stream property finalization.

Verifies that properties are correctly finalized when end_stream() is called.
"""

from aletheia.client import AletheiaClient
from aletheia.dsl import Signal


SIMPLE_DBC = {
    "version": "1.0",
    "messages": [{
        "id": 256,
        "name": "Test",
        "dlc": 8,
        "sender": "ECU",
        "signals": [{
            "name": "Speed",
            "startBit": 0,
            "length": 16,
            "byteOrder": "little_endian",
            "signed": False,
            "factor": 1.0,
            "offset": 0.0,
            "minimum": 0.0,
            "maximum": 65535.0,
            "unit": "kph",
            "presence": "always",
        }],
    }],
}


# Two-message DBC: the LTL predicate references Speed (from Msg256), but
# tests below only send frames of Msg512, so Speed is never observed.
TWO_MESSAGE_DBC = {
    "version": "1.0",
    "messages": [
        {
            "id": 256,
            "name": "Msg256",
            "dlc": 8,
            "sender": "ECU",
            "signals": [{
                "name": "Speed",
                "startBit": 0,
                "length": 16,
                "byteOrder": "little_endian",
                "signed": False,
                "factor": 1.0,
                "offset": 0.0,
                "minimum": 0.0,
                "maximum": 65535.0,
                "unit": "kph",
                "presence": "always",
            }],
        },
        {
            "id": 512,
            "name": "Msg512",
            "dlc": 8,
            "sender": "ECU",
            "signals": [{
                "name": "Rpm",
                "startBit": 0,
                "length": 16,
                "byteOrder": "little_endian",
                "signed": False,
                "factor": 1.0,
                "offset": 0.0,
                "minimum": 0.0,
                "maximum": 65535.0,
                "unit": "rpm",
                "presence": "always",
            }],
        },
    ],
}


class TestEndOfStreamFinalization:
    """End-of-stream property finalization."""

    def test_always_satisfied_multi_frame(self) -> None:
        """Always property that holds → satisfaction at end-of-stream."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            for i in range(5):
                client.send_frame(i * 1000, 256, 8, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            assert results[0]["status"] == "holds"

    def test_changed_by_never_one_frame(self) -> None:
        """1-frame changed_by(0).never() → unresolved (Kleene Unknown).

        With a single frame the ``changed_by(0)`` atomic has no prior
        observation to compare against, so it finalises to Unsure. The
        negation stays Unsure (Kleene fixed point), and ``Always`` on a
        non-empty trace leaves behind an ``And (Not Atomic) (Always ...)``
        in the Rosu progression whose Kleene conjunction is
        ``Unsure ∧ Holds = Unsure``.
        """
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").changed_by(0).never().to_dict()
            ])
            client.start_stream()
            client.send_frame(0, 256, 8, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            # Three-valued Kleene: never-resolved atomic → Unsure.
            assert results[0]["status"] == "unresolved"

    def test_always_zero_frames(self) -> None:
        """0-frame Always → satisfaction (vacuously true per standard LTLf)."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            # Standard LTLf: G φ on empty trace is vacuously true
            assert results[0]["status"] == "holds"

    def test_eventually_never_satisfied(self) -> None:
        """Eventually never satisfied → violation at end-of-stream."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").greater_than(1000).eventually().to_dict()
            ])
            client.start_stream()
            for i in range(5):
                client.send_frame(i * 1000, 256, 8, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            assert results[0]["status"] == "fails"
            assert "Eventually" in results[0].get("reason", "")

    def test_multiple_properties_mixed(self) -> None:
        """Multiple properties: some hold, some fail at end-of-stream."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                # Property 0: Always(Speed < 100) — will hold
                Signal("Speed").less_than(100).always().to_dict(),
                # Property 1: Eventually(Speed > 1000) — will fail
                Signal("Speed").greater_than(1000).eventually().to_dict(),
            ])
            client.start_stream()
            for i in range(5):
                client.send_frame(i * 1000, 256, 8, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 2
            # Property 0: satisfaction
            assert results[0]["status"] == "holds"
            # Property 1: violation
            assert results[1]["status"] == "fails"

    def test_results_field_present(self) -> None:
        """end_stream() response always has 'results' field."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            client.send_frame(0, 256, 8, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert "results" in resp
            assert resp["status"] == "complete"

    def test_no_properties_empty_results(self) -> None:
        """Stream with no properties → empty results list."""
        with AletheiaClient() as client:
            client.parse_dbc(SIMPLE_DBC)
            client.set_properties([])
            client.start_stream()
            client.send_frame(0, 256, 8, bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 0


class TestMissingSignalFinalization:
    """End-of-stream finalization when the referenced signal is never observed.

    These tests pin how Always/Release/Eventually/Until behave when the atomic
    predicate's signal is absent from every frame in the stream. Under the
    three-valued Kleene ``FinalVerdict`` (Holds / Fails / Unsure), an atomic
    whose signal was never observed finalises to Unsure — matching the
    denotational semantics ``⟦ Atomic p ⟧ σ = Unknown`` when p's signal never
    appears in σ.

    For ``Always(Atomic n)``: the Rosu progression emits
    ``And (Atomic n) (Always (Atomic n))`` and the absorption rule
    ``And φ (Always ψ) → Always ψ`` is guarded by ``finalizesHolds φ = true``,
    which is false for bare Atomic (finalizeL Atomic = Unsure). So the And
    hangs around and ``finalizeL (And (Atomic n) (Always _))`` reduces via
    Kleene conjunction ``Unsure ∧ Holds = Unsure``.

    Similarly ``Eventually(Atomic n)`` progresses to
    ``Or (Atomic n) (Eventually (Atomic n))`` and the guarding
    ``finalizesFails φ = true`` is also false under Path G's three-valued
    finalisation, so the Or persists and finalises via ``Unsure ∨ Fails =
    Unsure`` — a strictly stronger signal than the pre-Path-G Fails.
    """

    def test_always_zero_frames_missing_signal(self) -> None:
        """0 frames, signal never observed → Holds (vacuous via finalizeL)."""
        with AletheiaClient() as client:
            client.parse_dbc(TWO_MESSAGE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            assert results[0]["status"] == "holds"

    def test_always_never_observed_one_frame(self) -> None:
        """1 frame of a DIFFERENT message → Unresolved (Kleene Unknown).

        Sending a single Msg512 frame (no Speed) leaves the inner Atomic
        unresolved. Under three-valued Kleene finalisation this propagates
        through ``And (Atomic n) (Always _)`` as ``Unsure ∧ Holds = Unsure``.
        """
        with AletheiaClient() as client:
            client.parse_dbc(TWO_MESSAGE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            client.send_frame(0, 512, 8, bytearray([5, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            # Path G: never-resolved atomic → Unsure, propagated via Kleene And.
            assert results[0]["status"] == "unresolved"

    def test_always_never_observed_many_frames(self) -> None:
        """5 frames of Msg512 → Unresolved (persists regardless of count)."""
        with AletheiaClient() as client:
            client.parse_dbc(TWO_MESSAGE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            for i in range(5):
                client.send_frame(i * 1000, 512, 8,
                                  bytearray([5, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            assert results[0]["status"] == "unresolved"

    def test_eventually_never_observed_is_consistent(self) -> None:
        """Eventually(missing signal) → Unresolved at N ≥ 1 frames.

        Under Path G's three-valued finalisation the absorption rule
        ``Or φ (Eventually ψ) → Eventually ψ`` is guarded by
        ``finalizesFails φ = true``, which is false when φ is a bare Atomic
        (finalizeL Atomic = Unsure). The Or persists and finalises via the
        Kleene disjunction ``Unsure ∨ Fails = Unsure``.

        Contrast with the 0-frame case below, where there is no progression
        and finalizeL is applied directly to ``Eventually _`` → Fails.
        """
        with AletheiaClient() as client:
            client.parse_dbc(TWO_MESSAGE_DBC)
            client.set_properties([
                Signal("Speed").greater_than(10).eventually().to_dict()
            ])
            client.start_stream()
            for i in range(5):
                client.send_frame(i * 1000, 512, 8,
                                  bytearray([5, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            assert results[0]["status"] == "unresolved"

    def test_eventually_zero_frames_missing_signal(self) -> None:
        """0 frames → Eventually still Fails (liveness, no vacuous truth)."""
        with AletheiaClient() as client:
            client.parse_dbc(TWO_MESSAGE_DBC)
            client.set_properties([
                Signal("Speed").greater_than(10).eventually().to_dict()
            ])
            client.start_stream()
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            assert results[0]["status"] == "fails"

    def test_always_signal_recovers_after_missing(self) -> None:
        """Signal missing for first N frames then arriving → Holds.

        Confirms the bug only bites when the signal is missing for the
        ENTIRE stream. Once Speed is observed at least once with a
        true value, the absorption hanging on `And (Atomic) (Always ...)`
        collapses back to `Always (Atomic)` via `combineAnd Satisfied l`.
        """
        with AletheiaClient() as client:
            client.parse_dbc(TWO_MESSAGE_DBC)
            client.set_properties([
                Signal("Speed").less_than(100).always().to_dict()
            ])
            client.start_stream()
            # Three frames of Msg512 (Speed absent)
            for i in range(3):
                client.send_frame(i * 1000, 512, 8,
                                  bytearray([5, 0, 0, 0, 0, 0, 0, 0]))
            # Two frames of Msg256 with Speed = 10 (< 100)
            client.send_frame(3000, 256, 8,
                              bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            client.send_frame(4000, 256, 8,
                              bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
            resp = client.end_stream()
            assert resp["status"] == "complete"
            results = resp["results"]
            assert len(results) == 1
            assert results[0]["status"] == "holds"
