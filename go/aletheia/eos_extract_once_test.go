// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// End-of-stream enrichment runs ONE extraction pass per frame, not per
// property. These tests pin the extract-once shape of Client.EndStream:
// the frame loop runs at most once per EndStream (one full-frame extraction
// per last-seen frame, merged first-frame-wins, early break once every
// wanted signal has a value) and its result is distributed to every
// Fails/Unresolved entry. MockBackend records one
// `<binary:extractAllSignals>` sentinel per logical extraction (its binary
// path returns ErrBinaryPathUnsupported, so the JSON fallback records once),
// which makes the FFI-call cardinality directly observable via Inputs().

package aletheia_test

import (
	"bytes"
	"log/slog"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// countExtractCalls counts the extraction sentinels recorded by the mock.
func countExtractCalls(mock *aletheia.MockBackend) int {
	n := 0
	for _, in := range mock.Inputs() {
		if in == "<binary:extractAllSignals>" {
			n++
		}
	}
	return n
}

// twoSignalProperties returns two properties over disjoint signals, so the
// EOS union of wanted signals is {SigA, SigB}.
func twoSignalProperties() []aletheia.Formula {
	return []aletheia.Formula{
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
			Signal: "SigA", Value: aletheia.IntRational(10),
		}}},
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
			Signal: "SigB", Value: aletheia.IntRational(10),
		}}},
	}
}

// sendStandardFrame sends one zero-payload 8-byte frame on a standard CAN id.
func sendStandardFrame(t *testing.T, c *aletheia.Client, id uint16, tsMicros int64) {
	t.Helper()
	sid, err := aletheia.NewStandardID(id)
	if err != nil {
		t.Fatalf("NewStandardID(%#x): %v", id, err)
	}
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(ctx, aletheia.Timestamp{Microseconds: tsMicros}, sid, dlc8(), data, nil, nil); err != nil {
		t.Fatalf("SendFrame %#x: %v", id, err)
	}
}

func TestEndStream_ThreePropertiesShareOneExtractionPass(t *testing.T) {
	// Two last-seen frames and three failing properties (P0 wants SigA,
	// P1 wants SigB, P2 wants SigA again): the property-outer shape would
	// run a frame walk per property — 4 extractions here (P2 re-walks both
	// frames after P0/P1 consumed the two queued responses) and a naive
	// P×F sweep 6 — while the extract-once shape extracts exactly twice
	// (once per last-seen frame), then distributes the merged map filtered
	// per diagnostic, sharing SigA's single extraction between P0 and P2.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 0x100 @ t=0
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 0x100 @ t=1000 (overwrites last 0x100)
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 0x200 @ t=2000
		aletheia.Respond(`{
			"status":"complete",
			"results":[
				{"property_index":0,"status":"fails","timestamp":2000,"reason":"eventually unmet"},
				{"property_index":1,"status":"fails","timestamp":2000,"reason":"eventually unmet"},
				{"property_index":2,"status":"fails","timestamp":2000,"reason":"eventually unmet"}
			]
		}`), // EndStream
		aletheia.Respond(`{"status":"success","values":[{"name":"SigA","value":5}],"errors":[],"absent":[]}`), // EOS extraction, frame 0x100 (sorted first)
		aletheia.Respond(`{"status":"success","values":[{"name":"SigB","value":7}],"errors":[],"absent":[]}`), // EOS extraction, frame 0x200
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	properties := append(twoSignalProperties(),
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "SigA", Value: aletheia.IntRational(3),
		}}})
	if err := c.SetProperties(ctx, properties); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	sendStandardFrame(t, c, 0x100, 0)
	sendStandardFrame(t, c, 0x100, 1000)
	sendStandardFrame(t, c, 0x200, 2000)

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if got := countExtractCalls(mock); got != 2 {
		t.Errorf("expected 2 extraction calls (one per last-seen frame), got %d", got)
	}
	if len(sr.Results) != 3 {
		t.Fatalf("expected 3 results, got %d", len(sr.Results))
	}
	enrichA := sr.Results[0].Enrichment
	if enrichA == nil {
		t.Fatal("expected enrichment on result 0")
	}
	if len(enrichA.Signals) != 1 || enrichA.Signals["SigA"] != aletheia.IntRational(5) {
		t.Errorf("result 0: expected Signals {SigA: 5}, got %v", enrichA.Signals)
	}
	if !strings.Contains(enrichA.EnrichedReason, "SigA = 5") {
		t.Errorf("result 0: EnrichedReason = %q, want SigA value", enrichA.EnrichedReason)
	}
	enrichB := sr.Results[1].Enrichment
	if enrichB == nil {
		t.Fatal("expected enrichment on result 1")
	}
	if len(enrichB.Signals) != 1 || enrichB.Signals["SigB"] != aletheia.IntRational(7) {
		t.Errorf("result 1: expected Signals {SigB: 7}, got %v", enrichB.Signals)
	}
	enrichA2 := sr.Results[2].Enrichment
	if enrichA2 == nil {
		t.Fatal("expected enrichment on result 2")
	}
	if len(enrichA2.Signals) != 1 || enrichA2.Signals["SigA"] != aletheia.IntRational(5) {
		t.Errorf("result 2: expected the shared Signals {SigA: 5}, got %v", enrichA2.Signals)
	}
}

func TestEndStream_FrameLoopBreaksEarlyOnceUnionCovered(t *testing.T) {
	// The first (lowest-CAN-id) frame's extraction already supplies both
	// properties' signals, so the second last-seen frame is never extracted:
	// exactly one extraction call, and only one extraction response is
	// queued (a second attempt would exhaust the mock queue and surface as
	// a second sentinel, failing the count below).
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 0x100
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 0x200
		aletheia.Respond(`{
			"status":"complete",
			"results":[
				{"property_index":0,"status":"fails","timestamp":1000,"reason":"eventually unmet"},
				{"property_index":1,"status":"fails","timestamp":1000,"reason":"eventually unmet"}
			]
		}`), // EndStream
		aletheia.Respond(`{"status":"success","values":[{"name":"SigA","value":5},{"name":"SigB","value":7}],"errors":[],"absent":[]}`), // EOS extraction, frame 0x100 covers the union
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties(ctx, twoSignalProperties()); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	sendStandardFrame(t, c, 0x100, 0)
	sendStandardFrame(t, c, 0x200, 1000)

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if got := countExtractCalls(mock); got != 1 {
		t.Errorf("expected 1 extraction call (union covered by frame 0x100), got %d", got)
	}
	if len(sr.Results) != 2 {
		t.Fatalf("expected 2 results, got %d", len(sr.Results))
	}
	if e := sr.Results[0].Enrichment; e == nil || e.Signals["SigA"] != aletheia.IntRational(5) {
		t.Errorf("result 0: expected SigA=5 enrichment, got %+v", e)
	}
	if e := sr.Results[1].Enrichment; e == nil || e.Signals["SigB"] != aletheia.IntRational(7) {
		t.Errorf("result 1: expected SigB=7 enrichment, got %+v", e)
	}
}

func TestEndStream_MergeIsFirstFrameWins(t *testing.T) {
	// Discriminator for the merge direction. Frame 0x100 (lower CAN id, so
	// extracted first in the (CAN ID value, extended) order) reports SigA=1;
	// frame 0x200 reports SigA=2 AND SigB=3. The union of wanted signals is
	// {SigA, SigB} and SigB is still missing after frame 0x100, so the early
	// break does NOT fire and both frames are extracted (2 sentinels).
	// First-frame-wins keeps SigA=1 from frame 0x100 — an overwrite/last-wins
	// merge would surface SigA=2 — while SigB=3 arrives from frame 0x200.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 0x100
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 0x200
		aletheia.Respond(`{
			"status":"complete",
			"results":[
				{"property_index":0,"status":"fails","timestamp":1000,"reason":"eventually unmet"},
				{"property_index":1,"status":"fails","timestamp":1000,"reason":"eventually unmet"}
			]
		}`), // EndStream
		aletheia.Respond(`{"status":"success","values":[{"name":"SigA","value":1}],"errors":[],"absent":[]}`),                           // EOS extraction, frame 0x100 (first)
		aletheia.Respond(`{"status":"success","values":[{"name":"SigA","value":2},{"name":"SigB","value":3}],"errors":[],"absent":[]}`), // EOS extraction, frame 0x200 (second — its SigA must lose)
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties(ctx, twoSignalProperties()); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	sendStandardFrame(t, c, 0x100, 0)
	sendStandardFrame(t, c, 0x200, 1000)

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if got := countExtractCalls(mock); got != 2 {
		t.Errorf("expected 2 extraction calls (SigB missing after frame 0x100), got %d", got)
	}
	if len(sr.Results) != 2 {
		t.Fatalf("expected 2 results, got %d", len(sr.Results))
	}
	enrichA := sr.Results[0].Enrichment
	if enrichA == nil {
		t.Fatal("expected enrichment on result 0")
	}
	if got := enrichA.Signals["SigA"]; got != aletheia.IntRational(1) {
		t.Errorf("SigA = %v, want 1 (first frame wins; 2 would mean a last-wins merge)", got)
	}
	enrichB := sr.Results[1].Enrichment
	if enrichB == nil {
		t.Fatal("expected enrichment on result 1")
	}
	if got := enrichB.Signals["SigB"]; got != aletheia.IntRational(3) {
		t.Errorf("SigB = %v, want 3 (from frame 0x200)", got)
	}
}

func TestEndStream_AllSatisfiedMakesNoExtractionCalls(t *testing.T) {
	// No Fails/Unresolved entries → no frame snapshot, no extraction pass,
	// and no enrichment — even though a frame is cached (no extraction
	// response is queued, so an attempt would surface as a sentinel).
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[
				{"property_index":0,"status":"holds"},
				{"property_index":1,"status":"holds"}
			]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties(ctx, twoSignalProperties()); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	sendStandardFrame(t, c, 0x100, 0)

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if got := countExtractCalls(mock); got != 0 {
		t.Errorf("expected 0 extraction calls for an all-Holds stream, got %d", got)
	}
	for i, pr := range sr.Results {
		if pr.Enrichment != nil {
			t.Errorf("result %d: expected nil Enrichment on Holds, got %+v", i, pr.Enrichment)
		}
	}
}

func TestEndStream_FailedExtractionWarnsOncePerFrame(t *testing.T) {
	// Two failing properties over one last-seen frame whose extraction
	// errors: the shared pass attempts the frame once (one sentinel) and
	// emits ONE enrichment.extraction_failed warning — the property-outer
	// shape warned once per property. Both entries still get the fallback
	// enrichment.
	var buf bytes.Buffer
	logger := slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelWarn}))
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[
				{"property_index":0,"status":"fails","timestamp":1000,"reason":"eventually unmet"},
				{"property_index":1,"status":"fails","timestamp":1000,"reason":"eventually unmet"}
			]
		}`), // EndStream
		aletheia.Respond(`{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}`), // EOS extraction fails
	)
	c, err := aletheia.NewClient(mock, aletheia.WithLogger(logger))
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties(ctx, twoSignalProperties()); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	sendStandardFrame(t, c, 0x100, 0)

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if got := countExtractCalls(mock); got != 1 {
		t.Errorf("expected 1 extraction attempt for the single frame, got %d", got)
	}
	if got := strings.Count(buf.String(), "enrichment.extraction_failed"); got != 1 {
		t.Errorf("expected 1 extraction_failed warning (once per frame), got %d in:\n%s", got, buf.String())
	}
	for i, pr := range sr.Results {
		if pr.Enrichment == nil {
			t.Fatalf("result %d: expected fallback enrichment despite extraction failure", i)
		}
		if pr.Enrichment.Signals != nil {
			t.Errorf("result %d: expected nil Signals after failed extraction, got %v", i, pr.Enrichment.Signals)
		}
		if !strings.HasPrefix(pr.Enrichment.EnrichedReason, "violated: ") {
			t.Errorf("result %d: EnrichedReason = %q, want the formula-description fallback", i, pr.Enrichment.EnrichedReason)
		}
	}
}

func TestEndStream_OOBIndexExcludedValidEntryStillEnriched(t *testing.T) {
	// An out-of-bounds property_index is warned once and excluded — it gets
	// no enrichment and drives no extraction of its own — while the valid
	// entry in the same finalization batch is still enriched.
	var buf bytes.Buffer
	logger := slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelWarn}))
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties (1 property)
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[
				{"property_index":0,"status":"fails","timestamp":1000,"reason":"eventually unmet"},
				{"property_index":3,"status":"fails","timestamp":1000,"reason":"eventually unmet"}
			]
		}`), // EndStream
		aletheia.Respond(`{"status":"success","values":[{"name":"SigA","value":5}],"errors":[],"absent":[]}`), // EOS extraction
	)
	c, err := aletheia.NewClient(mock, aletheia.WithLogger(logger))
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties(ctx, twoSignalProperties()[:1]); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}
	sendStandardFrame(t, c, 0x100, 0)

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	output := buf.String()
	if got := strings.Count(output, "enrichment.property_index_oob"); got != 1 {
		t.Errorf("expected 1 property_index_oob warning, got %d in:\n%s", got, output)
	}
	if !strings.Contains(output, "index=3") || !strings.Contains(output, "count=1") {
		t.Errorf("expected index=3 count=1 in the OOB warning, got:\n%s", output)
	}
	if got := countExtractCalls(mock); got != 1 {
		t.Errorf("expected 1 extraction call, got %d", got)
	}
	if e := sr.Results[0].Enrichment; e == nil || e.Signals["SigA"] != aletheia.IntRational(5) {
		t.Errorf("result 0: expected SigA=5 enrichment, got %+v", e)
	}
	if sr.Results[1].Enrichment != nil {
		t.Errorf("result 1 (OOB): expected nil Enrichment, got %+v", sr.Results[1].Enrichment)
	}
}

func TestEndStream_NoTrackedFramesAttachesFallbackWithoutExtraction(t *testing.T) {
	// Zero tracked frames → the extraction pass has nothing to iterate:
	// zero FFI calls (no extraction response is queued, so an attempt would
	// surface as a sentinel), yet the Fails entry still carries the
	// enrichment object with the empty-values fallback reason.
	//
	// This is also the public pin for the empty-union skip's observable
	// contract (0 extractions + enrichment always attached): an empty
	// diag.Signals list itself is unreachable through the public formula
	// surface (every serializable formula has at least one Atomic leaf and
	// collectSignals keeps even an empty signal name), and fabricating it
	// from an external test package would require injecting private state,
	// which is out per the test-via-interface rule — the skip's condition is
	// separately covered by the sentinel-count pins in this file (inverting
	// it would zero out ThreePropertiesShareOneExtractionPass).
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","timestamp":1000,"reason":"eventually unmet"}]
		}`), // EndStream — no frame ever sent, no extraction response queued
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties(ctx, twoSignalProperties()); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if got := countExtractCalls(mock); got != 0 {
		t.Errorf("expected 0 extraction calls with no tracked frames, got %d", got)
	}
	if len(sr.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(sr.Results))
	}
	e := sr.Results[0].Enrichment
	if e == nil {
		t.Fatal("expected enrichment attached despite the empty extraction pass")
	}
	if e.Signals != nil {
		t.Errorf("expected nil Signals, got %v", e.Signals)
	}
	if !strings.HasPrefix(e.EnrichedReason, "violated: ") || !strings.Contains(e.EnrichedReason, "[core: eventually unmet]") {
		t.Errorf("EnrichedReason = %q, want the empty-values fallback with the core suffix", e.EnrichedReason)
	}
}
