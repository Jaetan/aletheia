"""AGDA-B-9.2 closure: re-evaluating a Satisfied proc must not produce a
spurious Violated counterexample on subsequent frames.

The fix in ``Aletheia.Protocol.StreamState.Internals.classifyStepResult`` returns
``complete`` (drops the property from the active iteration set) on Satisfied,
not ``advance prop`` (which kept the proc and re-stepped it).  The latent bug
this closes: top-level ``Until`` / ``Release`` / ``MetricUntil`` /
``MetricRelease`` / raw ``Atomic`` / ``And``/``Or``-of-atomic shapes can return
Satisfied at one frame and Violated at the next.

The DSL (``Signal(...).cmp(...).always()`` / ``.eventually()``) wraps user
predicates so the typical workflow never reaches the unsafe shapes; this test
reaches them by submitting a raw ``Until`` formula via the JSON wire path.
"""
from __future__ import annotations

from typing import cast

from aletheia import AletheiaClient, Signal
from aletheia.dsl import UntilFormula
from aletheia.protocols import DBCDefinition, DLCCode


def test_raw_until_satisfied_drops_from_active_set(simple_dbc: DBCDefinition) -> None:
    """Raw ``Until(TestSignal == 1, TestSignal == 100)`` goes Satisfied at the
    frame where ``TestSignal == 100`` holds; the next frame where neither atom
    holds must Ack (the property is no longer in the active set), not emit a
    spurious Violated.

    Pre-fix runtime behaviour on this trace was: y₁ Satisfied via
    ``combineOr Satisfied _ = Satisfied``; y₂ Violated via
    ``combineOr (Violated _) (Violated _) = Violated`` — a false counterexample
    for a property already declared satisfied.
    """
    left_pred = Signal("TestSignal").equals(1)
    right_pred = Signal("TestSignal").equals(100)

    raw_until_formula = cast(UntilFormula, {
        "operator": "until",
        "left": left_pred.to_formula(),
        "right": right_pred.to_formula(),
    })

    with AletheiaClient() as client:
        client.parse_dbc(simple_dbc)
        client.set_properties([raw_until_formula])
        client.start_stream()

        # Frame y₁ — TestSignal = 100 — `right` atom holds; Until is Satisfied.
        # The property is dropped from the active iteration set (`complete`).
        # R23 — AGDA-D-12.1: mid-stream Satisfaction is now surfaced in a
        # PropertyBatchResponse (was previously wire-silent Ack); the
        # holds entry carries the property index.
        response_y1 = client.send_frame(
            timestamp=1000,
            can_id=256,
            dlc=DLCCode(8),
            data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]),
        )
        assert response_y1.get("type") == "property_batch", (
            f"Expected property_batch at y₁ (mid-stream Satisfaction); got {response_y1!r}"
        )
        assert len(response_y1["results"]) == 1
        assert response_y1["results"][0]["status"] == "holds"

        # Frame y₂ — TestSignal = 50 — both atoms False.  Pre-fix this would
        # re-evaluate the Until proc and emit a false counterexample; post-fix
        # the proc is no longer in the active set, so the response is Ack
        # (no further events — the property already emitted its Satisfaction
        # at y₁).
        response_y2 = client.send_frame(
            timestamp=2000,
            can_id=256,
            dlc=DLCCode(8),
            data=bytearray([50, 0, 0, 0, 0, 0, 0, 0]),
        )
        assert response_y2.get("status") == "ack", (
            "Expected ack at y₂ — Until was Satisfied at y₁ so the proc must "
            "not be re-evaluated; pre-fix runtime emitted a spurious Violated "
            f"here. Got {response_y2!r}"
        )

        client.end_stream()


def test_eventually_satisfied_midstream_absent_from_endstream(simple_dbc: DBCDefinition) -> None:
    """Eventually that satisfies mid-stream is ABSENT from the EndStream
    ``Complete.results`` list (post-fix observability shift).

    Pre-fix `classifyStepResult Satisfied prop = advance prop` kept the
    Eventually proc in the active set even after satisfaction; at EndStream
    `finalizeL (Eventually _) = Fails EventuallyUnsatisfied` returned a false
    negative for the satisfied property.  Concrete pre-fix observation on
    `Eventually(TestSignal == 42)` with TestSignal=42 at y₂:
    ``EndStream → {'status': 'fails', 'reason': 'Eventually: never satisfied
    before end of stream'}``.

    Post-fix `classifyStepResult Satisfied _ = complete` drops the property
    from the active set on satisfaction; at EndStream the property is
    omitted from `Complete.results` rather than misclassified.  Strictly
    better than a false-negative `Fails` verdict; lifting `Satisfaction`
    emission into the streaming dispatch (so users get an explicit positive
    verdict) is a separate enhancement.
    """
    with AletheiaClient() as client:
        client.parse_dbc(simple_dbc)
        client.set_properties([
            Signal("TestSignal").equals(42).eventually().to_dict()
        ])
        client.start_stream()
        # y₁: TestSignal != 42 — Eventually proc continues.
        client.send_frame(1000, 256, DLCCode(8), bytearray([10, 0, 0, 0, 0, 0, 0, 0]))
        # y₂: TestSignal == 42 — Eventually goes Satisfied; prop drops from active set.
        client.send_frame(2000, 256, DLCCode(8), bytearray([42, 0, 0, 0, 0, 0, 0, 0]))
        # y₃: TestSignal != 42 — irrelevant, prop is no longer in active set.
        client.send_frame(3000, 256, DLCCode(8), bytearray([99, 0, 0, 0, 0, 0, 0, 0]))

        end = client.end_stream()
        assert end.get("status") == "complete", (
            f"EndStream status should be 'complete'; got {end!r}"
        )
        # The property is absent from results — pre-fix it was erroneously
        # listed as 'fails' / 'Eventually: never satisfied'.
        assert end.get("results") == [], (
            "Eventually that satisfied at y₂ should be absent from EndStream "
            f"results (post-fix observability shift); got {end!r}.  Pre-fix "
            "would have emitted a false-negative 'fails' verdict here."
        )


def test_eventually_completes_cleanly_on_first_witness(simple_dbc: DBCDefinition) -> None:
    """``stepL-eventually-never-violated`` proves Eventually-wrapped properties
    never produce Violated; combined with ``complete`` on Satisfied, an
    Eventually property drops from the active set on first witness.  Subsequent
    frames must Ack regardless of whether the inner predicate holds.
    """
    with AletheiaClient() as client:
        client.parse_dbc(simple_dbc)
        client.set_properties([
            Signal("TestSignal").equals(42).eventually().to_dict()
        ])
        client.start_stream()

        # y₁: TestSignal != 42 — Continue, prop stays in active set.
        response_y1 = client.send_frame(
            timestamp=1000,
            can_id=256,
            dlc=DLCCode(8),
            data=bytearray([10, 0, 0, 0, 0, 0, 0, 0]),
        )
        assert response_y1.get("status") == "ack"

        # y₂: TestSignal == 42 — Satisfied; prop drops from active set.
        # R23 — AGDA-D-12.1: emits PropertyBatchResponse with the Satisfaction.
        response_y2 = client.send_frame(
            timestamp=2000,
            can_id=256,
            dlc=DLCCode(8),
            data=bytearray([42, 0, 0, 0, 0, 0, 0, 0]),
        )
        assert response_y2.get("type") == "property_batch"
        assert len(response_y2["results"]) == 1
        assert response_y2["results"][0]["status"] == "holds"

        # y₃, y₄: TestSignal arbitrary — proc is no longer in active set, so
        # response is unconditionally Ack regardless of predicate value.
        for ts, val in [(3000, 99), (4000, 0)]:
            response = client.send_frame(
                timestamp=ts,
                can_id=256,
                dlc=DLCCode(8),
                data=bytearray([val, 0, 0, 0, 0, 0, 0, 0]),
            )
            assert response.get("status") == "ack", (
                f"y@{ts}: Eventually proc dropped after y₂ — response should "
                f"be Ack regardless of TestSignal value; got {response!r}"
            )

        client.end_stream()


def test_multi_event_frame_satisfaction_plus_violation(simple_dbc: DBCDefinition) -> None:
    """R23 — AGDA-D-12.1: a single frame can produce both a mid-stream
    Satisfaction AND a terminal Violation in the same PropertyBatch.

    Setup: two properties — index 0 is `eventually(TestSignal == 100)`
    (completes on first witness), index 1 is `always(TestSignal < 50)`
    (violates at the same frame because TestSignal = 100 > 50).
    The frame TestSignal = 100 fires BOTH events in source-order: a
    Satisfaction on property 0, then a Violation on property 1.

    Pre-R23 the Satisfaction would have been wire-silent (the property
    was just dropped from the active set); the Violation alone reached
    the user.  Post-R23 both events surface in `results` with
    `[Satisfaction, Violation]` source-order per the Agda
    dispatchIterResult invariant.
    """
    eventually_prop = Signal("TestSignal").equals(100).eventually()
    always_prop = Signal("TestSignal").less_than(50).always()

    with AletheiaClient() as client:
        client.parse_dbc(simple_dbc)
        client.set_properties([eventually_prop.to_dict(), always_prop.to_dict()])
        client.start_stream()

        # TestSignal = 100 fires BOTH:
        #  - property 0 (eventually(== 100)): Satisfied → complete(0)
        #  - property 1 (always(< 50)):       Violated  → halt(1)
        response = client.send_frame(
            timestamp=1000,
            can_id=256,
            dlc=DLCCode(8),
            data=bytearray([100, 0, 0, 0, 0, 0, 0, 0]),
        )

        assert response.get("type") == "property_batch", response
        assert len(response["results"]) == 2, response["results"]
        # Source-order: satisfaction first, violation last.
        sat, viol = response["results"]
        assert sat["status"] == "holds"
        assert sat["property_index"] == {"numerator": 0, "denominator": 1}
        assert viol["status"] == "fails"
        assert viol["property_index"] == {"numerator": 1, "denominator": 1}

        client.end_stream()
