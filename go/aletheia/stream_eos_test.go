//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// ---------------------------------------------------------------------------
// End-of-stream three-valued Kleene finalization (Path G, 2026-04-09)
// ---------------------------------------------------------------------------
//
// These tests mirror python/tests/test_eos_finalization.py::TestMissingSignalFinalization
// to give Go client-level coverage of the Unresolved (Unsure) verdict. They
// complement TestStreamingLTL_Unresolved above with additional scenarios:
//
//   - Always + never-observed signal after many frames → Unresolved
//   - changed_by on a one-frame trace → Unresolved
//   - Eventually + never-observed signal → Unresolved (regression guard
//     against the pre-Path-G collapse to Fails)
//   - Eventually on empty trace → Fails (liveness, no vacuous truth)
//   - Always on empty trace → Holds (vacuous LTLf)
//   - K3 truth-table combinations via And/Or
//   - Enrichment populated for Unresolved results when diagnostics exist
//
// These drive a mock: what is under test here is the binding's own path from
// the wire to a verdict and its enrichment, and the Python and C++ suites put
// the same verdicts to the library.

func TestEOS_AlwaysNeverObserved_ManyFrames(t *testing.T) {
	ctx := t.Context()
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: aletheia.IntRational(100),
		}}},
	},
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 1
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 2
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 3
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 4
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 5
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Atomic: predicate never resolved at end of stream"}]
		}`), // EndStream
	)
	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	for i := range 5 {
		ts := aletheia.Timestamp{Microseconds: int64(i) * 1000}
		if _, err := c.SendFrame(ctx, ts, sid, dlc8(), data, nil, nil); err != nil {
			t.Fatalf("SendFrame %d: %v", i, err)
		}
	}

	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Unresolved {
		t.Errorf("expected Unresolved after 5 frames without Speed, got %s",
			result.Results[0].Verdict)
	}
}

func TestEOS_ChangedByOneFrame_Unresolved(t *testing.T) {
	ctx := t.Context()
	// A single frame gives changed_by(0) no prior observation to compare
	// against, so its inner Atomic finalizes to Unsure. Under Kleene K3 the
	// negation stays Unsure and the Always absorption leaves an
	// And (Not Atomic) (Always _) which reduces via Unsure ∧ Holds = Unsure.
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Not{Inner: aletheia.Atomic{
			Predicate: aletheia.ChangedBy{Signal: "Speed", Delta: aletheia.IntRational(0)},
		}}},
	},
		aletheia.Respond(`{"status":"ack"}`), // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"ChangedBy: single-frame trace"}]
		}`), // EndStream
	)
	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{10, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data, nil, nil); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Unresolved {
		t.Errorf("expected Unresolved on one-frame changed_by, got %s",
			result.Results[0].Verdict)
	}
}

func TestEOS_EventuallyNeverObserved_Unresolved(t *testing.T) {
	ctx := t.Context()
	// A disjunction with an eventually on one side is not absorbed into that
	// side when the other side is undecided: the disjunction stands, and an
	// undecided side beside a failing one leaves the whole undecided.
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
			Signal: "Speed", Value: aletheia.IntRational(10),
		}}},
	},
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 1
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 2
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 3
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 4
		aletheia.Respond(`{"status":"ack"}`), // SendFrame 5
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Atomic: predicate never resolved at end of stream"}]
		}`), // EndStream
	)
	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	for i := range 5 {
		ts := aletheia.Timestamp{Microseconds: int64(i) * 1000}
		if _, err := c.SendFrame(ctx, ts, sid, dlc8(), data, nil, nil); err != nil {
			t.Fatalf("SendFrame %d: %v", i, err)
		}
	}

	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Unresolved {
		t.Errorf("expected Unresolved for Eventually on never-observed signal, got %s",
			result.Results[0].Verdict)
	}
}

func TestEOS_EventuallyZeroFrames_Fails(t *testing.T) {
	ctx := t.Context()
	// Against the case above, which saw a frame: on a trace with none, an
	// eventually fails outright. Nothing was left undecided, because nothing
	// was ever observed.
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
			Signal: "Speed", Value: aletheia.IntRational(10),
		}}},
	},
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","reason":"Eventually: never satisfied"}]
		}`), // EndStream
	)
	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Fails {
		t.Errorf("expected Fails for 0-frame Eventually, got %s",
			result.Results[0].Verdict)
	}
}

func TestEOS_AlwaysZeroFrames_Holds(t *testing.T) {
	ctx := t.Context()
	// Standard LTLf vacuous truth: G φ on the empty trace holds regardless
	// of whether φ's signal would be observable. Distinguishes the
	// empty-trace finalization path (direct on Always) from the non-empty
	// path (finalizeL after progression leaves an And behind).
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: aletheia.IntRational(100),
		}}},
	},
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"holds"}]
		}`), // EndStream
	)
	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Holds {
		t.Errorf("expected Holds for 0-frame Always, got %s",
			result.Results[0].Verdict)
	}
}

func TestEOS_K3Combination_UnresolvedAndHolds(t *testing.T) {
	ctx := t.Context()
	// Kleene truth table: Unsure ∧ Holds = Unsure. The And combinator with
	// one Unresolved operand and one Holds operand must surface as
	// Unresolved. Verifies the JSON status mapping and the Go Verdict
	// constant roundtrip on a representative K3 conjunction case.
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.And{
			Left: aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
				Signal: "Speed", Value: aletheia.IntRational(100),
			}}},
			Right: aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
				Signal: "Rpm", Value: aletheia.IntRational(100),
			}}},
		},
	},
		aletheia.Respond(`{"status":"ack"}`), // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"And: Unsure ∧ Holds = Unsure"}]
		}`), // EndStream
	)
	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data, nil, nil); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Unresolved {
		t.Errorf("expected Unresolved (Unsure ∧ Holds = Unsure), got %s",
			result.Results[0].Verdict)
	}
}

func TestEOS_K3Combination_UnresolvedOrFails(t *testing.T) {
	ctx := t.Context()
	// Kleene truth table: Unsure ∨ Fails = Unsure. An Or with one Unresolved
	// operand and one Fails operand must surface as Unresolved.
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.Or{
			Left: aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
				Signal: "Speed", Value: aletheia.IntRational(100),
			}}},
			Right: aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
				Signal: "Rpm", Value: aletheia.IntRational(999999),
			}}},
		},
	},
		aletheia.Respond(`{"status":"ack"}`), // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Or: Unsure ∨ Fails = Unsure"}]
		}`), // EndStream
	)
	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data, nil, nil); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Unresolved {
		t.Errorf("expected Unresolved (Unsure ∨ Fails = Unsure), got %s",
			result.Results[0].Verdict)
	}
}

func TestEOS_MixedVerdicts(t *testing.T) {
	ctx := t.Context()
	// Stream with three properties that finalize to different K3 verdicts.
	// Confirms the Go result decoder correctly parses and orders a mix of
	// Holds, Fails, and Unresolved in a single stream response.
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: aletheia.IntRational(1000),
		}}},
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
			Signal: "Speed", Value: aletheia.IntRational(999999),
		}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Rpm", Value: aletheia.IntRational(100),
		}}},
	},
		aletheia.Respond(`{"status":"ack"}`), // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[
				{"property_index":0,"status":"holds"},
				{"property_index":1,"status":"fails","timestamp":1000,"reason":"Eventually: never satisfied"},
				{"property_index":2,"status":"unresolved","reason":"Atomic: predicate never resolved"}
			]
		}`), // EndStream
	)
	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{10, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data, nil, nil); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 3 {
		t.Fatalf("expected 3 results, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Holds {
		t.Errorf("expected Results[0] Holds, got %s", result.Results[0].Verdict)
	}
	if result.Results[1].Verdict != aletheia.Fails {
		t.Errorf("expected Results[1] Fails, got %s", result.Results[1].Verdict)
	}
	if result.Results[2].Verdict != aletheia.Unresolved {
		t.Errorf("expected Results[2] Unresolved, got %s", result.Results[2].Verdict)
	}
}

func TestEOS_UnresolvedCarriesEnrichment(t *testing.T) {
	ctx := t.Context()
	// Client.EndStream runs enrichEndOfStream over Unresolved verdicts
	// (client_enrich.go, todo collection). Verify the enrichment field is populated
	// with FormulaDesc/CoreReason for an Unresolved result, parallel to the
	// Fails enrichment path exercised by TestEndStream_Enriched.
	c, _ := startedClientWith(t, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: aletheia.IntRational(100),
		}}},
	},
		aletheia.Respond(`{"status":"ack"}`), // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Atomic: predicate never resolved at end of stream"}]
		}`), // EndStream
	)
	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data, nil, nil); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	pr := result.Results[0]
	if pr.Verdict != aletheia.Unresolved {
		t.Fatalf("expected Unresolved, got %s", pr.Verdict)
	}
	if pr.Enrichment == nil {
		t.Fatal("expected Enrichment populated for Unresolved result, got nil")
	}
	if pr.Enrichment.CoreReason == "" {
		t.Error("expected CoreReason populated from raw Reason")
	}
	if pr.Enrichment.FormulaDesc == "" {
		t.Error("expected FormulaDesc populated from diagnostic")
	}
	if !strings.Contains(pr.Reason, "never resolved") {
		t.Errorf("expected raw Reason to mention 'never resolved', got %q", pr.Reason)
	}
}
