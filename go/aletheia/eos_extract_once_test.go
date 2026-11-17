//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// End-of-stream enrichment extracts once per last-seen frame, not once per
// property: one full-frame extraction per frame in CAN-ID order, merged
// first-frame-wins, stopping as soon as every wanted signal has a value, and
// the merged values are then handed to every failing or unresolved entry.
// The count is observable because the mock records one
// <binary:extractAllSignals> sentinel per extraction: its binary path answers
// ErrBinaryPathUnsupported, so each extraction reaches the JSON path once.

package aletheia_test

import (
	"bytes"
	"fmt"
	"log/slog"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// extractCalls is how many extractions the mock recorded.
func extractCalls(mock *aletheia.MockBackend) int {
	n := 0
	for _, in := range mock.Inputs() {
		if in == "<binary:extractAllSignals>" {
			n++
		}
	}
	return n
}

// twoSignalProperties are two properties over disjoint signals, so the union
// of wanted signals is SigA and SigB.
func twoSignalProperties() []aletheia.Formula {
	return []aletheia.Formula{
		aletheia.Eventually{Inner: gt("SigA", 10)},
		aletheia.Eventually{Inner: gt("SigB", 10)},
	}
}

// endStreamFails is an end-of-stream response failing the given properties.
func endStreamFails(indices ...int) aletheia.MockResponse {
	parts := make([]string, 0, len(indices))
	for _, i := range indices {
		parts = append(parts, fmt.Sprintf(`{"type":"property","property_index":%d,"status":"fails","timestamp":1000,"reason":"eventually unmet"}`, i))
	}
	return aletheia.Respond(`{"status":"complete","results":[` + strings.Join(parts, ",") + `],"warnings":[]}`)
}

// endStreamHolds is an end-of-stream response satisfying the given properties.
func endStreamHolds(indices ...int) aletheia.MockResponse {
	parts := make([]string, 0, len(indices))
	for _, i := range indices {
		parts = append(parts, fmt.Sprintf(`{"type":"property","property_index":%d,"status":"holds"}`, i))
	}
	return aletheia.Respond(`{"status":"complete","results":[` + strings.Join(parts, ",") + `],"warnings":[]}`)
}

// warnLog is a client option collecting warnings into the buffer it returns.
func warnLog() (aletheia.ClientOption, *bytes.Buffer) {
	var buf bytes.Buffer
	return aletheia.WithLogger(slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelWarn}))), &buf
}

// mustEndStream ends the stream and returns its verdicts.
func mustEndStream(t *testing.T, c *aletheia.Client, want int) []aletheia.PropertyResult {
	t.Helper()
	ctx := t.Context()
	sr, err := c.EndStream(ctx)
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(sr.Results) != want {
		t.Fatalf("expected %d results, got %d", want, len(sr.Results))
	}
	return sr.Results
}

// wantOneSignal asserts the result carries an enrichment whose only value is
// the named one.
func wantOneSignal(t *testing.T, pr aletheia.PropertyResult, name aletheia.SignalName, value int64) {
	t.Helper()
	if pr.Enrichment == nil {
		t.Fatalf("expected an enrichment, got none")
	}
	if len(pr.Enrichment.Signals) != 1 || pr.Enrichment.Signals[name] != aletheia.IntRational(value) {
		t.Errorf("Signals = %v, want %s = %d alone", pr.Enrichment.Signals, name, value)
	}
}

// Three failing properties over two last-seen frames extract twice, once per
// frame: the two properties wanting the same signal share its extraction. A
// walk per property would extract four times, and a property-by-frame sweep
// six.
func TestEndStream_ThreePropertiesShareOneExtractionPass(t *testing.T) {
	properties := append(twoSignalProperties(), aletheia.Eventually{Inner: lt("SigA", 3)})
	c, mock := startedClientWith(t, properties,
		aletheia.Respond(ack), aletheia.Respond(ack), aletheia.Respond(ack),
		endStreamFails(0, 1, 2),
		extractionOf("SigA", 5), // frame 0x100, extracted first
		extractionOf("SigB", 7), // frame 0x200
	)
	sendOn(t, c, 0x100, 0)
	sendOn(t, c, 0x100, 1000) // overwrites the last frame on 0x100
	sendOn(t, c, 0x200, 2000)

	results := mustEndStream(t, c, 3)
	if got := extractCalls(mock); got != 2 {
		t.Errorf("expected 2 extractions (one per last-seen frame), got %d", got)
	}
	wantOneSignal(t, results[0], "SigA", 5)
	wantOneSignal(t, results[1], "SigB", 7)
	wantOneSignal(t, results[2], "SigA", 5) // the shared extraction
	if !strings.Contains(results[0].Enrichment.EnrichedReason, "SigA = 5") {
		t.Errorf("EnrichedReason = %q, want the observed value", results[0].Enrichment.EnrichedReason)
	}
}

// The first frame already carries every wanted signal, so the second is never
// extracted; only one extraction response is queued, and a second attempt
// would record a sentinel.
func TestEndStream_FrameLoopBreaksEarlyOnceUnionCovered(t *testing.T) {
	c, mock := startedClientWith(t, twoSignalProperties(),
		aletheia.Respond(ack), aletheia.Respond(ack),
		endStreamFails(0, 1),
		extractionOf("SigA", 5, "SigB", 7), // frame 0x100 covers the union
	)
	sendOn(t, c, 0x100, 0)
	sendOn(t, c, 0x200, 1000)

	results := mustEndStream(t, c, 2)
	if got := extractCalls(mock); got != 1 {
		t.Errorf("expected 1 extraction (the union covered by the first frame), got %d", got)
	}
	wantOneSignal(t, results[0], "SigA", 5)
	wantOneSignal(t, results[1], "SigB", 7)
}

// Both frames carry SigA and only the second carries SigB, so both are
// extracted and the first frame's SigA wins: a last-wins merge would report
// the second frame's.
func TestEndStream_MergeIsFirstFrameWins(t *testing.T) {
	c, mock := startedClientWith(t, twoSignalProperties(),
		aletheia.Respond(ack), aletheia.Respond(ack),
		endStreamFails(0, 1),
		extractionOf("SigA", 1),            // frame 0x100, extracted first
		extractionOf("SigA", 2, "SigB", 3), // frame 0x200, whose SigA must lose
	)
	sendOn(t, c, 0x100, 0)
	sendOn(t, c, 0x200, 1000)

	results := mustEndStream(t, c, 2)
	if got := extractCalls(mock); got != 2 {
		t.Errorf("expected 2 extractions (SigB still missing after the first frame), got %d", got)
	}
	wantOneSignal(t, results[0], "SigA", 1)
	wantOneSignal(t, results[1], "SigB", 3)
}

// A stream whose properties all hold extracts nothing and enriches nothing,
// though a frame is cached; no extraction response is queued, so an attempt
// would record a sentinel.
func TestEndStream_AllSatisfiedMakesNoExtractionCalls(t *testing.T) {
	c, mock := startedClientWith(t, twoSignalProperties(), aletheia.Respond(ack), endStreamHolds(0, 1))
	sendOn(t, c, 0x100, 0)

	results := mustEndStream(t, c, 2)
	if got := extractCalls(mock); got != 0 {
		t.Errorf("expected no extraction for a stream that holds, got %d", got)
	}
	for i, pr := range results {
		if pr.Enrichment != nil {
			t.Errorf("result %d: expected no enrichment on a holding property, got %+v", i, pr.Enrichment)
		}
	}
}

// With no frame ever sent there is nothing to extract, and the failing entry
// still carries an enrichment with the fallback reason and the core's.
func TestEndStream_NoTrackedFramesAttachesFallbackWithoutExtraction(t *testing.T) {
	c, mock := startedClientWith(t, twoSignalProperties(), endStreamFails(0))

	results := mustEndStream(t, c, 1)
	if got := extractCalls(mock); got != 0 {
		t.Errorf("expected no extraction with no tracked frame, got %d", got)
	}
	e := results[0].Enrichment
	if e == nil {
		t.Fatal("expected an enrichment despite the empty extraction pass")
	}
	if e.Signals != nil {
		t.Errorf("expected no values, got %v", e.Signals)
	}
	if !strings.HasPrefix(e.EnrichedReason, "violated: ") || !strings.Contains(e.EnrichedReason, "[core: eventually unmet]") {
		t.Errorf("EnrichedReason = %q, want the fallback with the core's reason", e.EnrichedReason)
	}
}

// Diagnostics naming no signal extract no tracked frame, and the failing entry
// still carries the fallback reason with the core's. Every serializable
// formula has an atomic leaf and the signal collector keeps even an empty
// name, so the diagnostics are replaced by ones naming none: with two frames
// tracked, the frame loop stops at its head before the first extraction.
func TestEndStream_AnEmptyUnionExtractsNoTrackedFrame(t *testing.T) {
	c, mock := startedClientWith(t, twoSignalProperties(),
		aletheia.Respond(ack), aletheia.Respond(ack),
		endStreamFails(0),
		// Read only by a loop that extracts, so the count below is what refuses it.
		extractionOf("SigA", 5),
		extractionOf("SigB", 7),
	)
	signalless := aletheia.PropertyDiagnostic{FormulaDesc: "eventually(nothing)"}
	aletheia.SetDiagnostics(c, []aletheia.PropertyDiagnostic{signalless, signalless})
	sendOn(t, c, 0x100, 0)
	sendOn(t, c, 0x200, 1000)

	results := mustEndStream(t, c, 1)
	if got := extractCalls(mock); got != 0 {
		t.Errorf("expected no extraction for an empty union, got %d", got)
	}
	e := results[0].Enrichment
	if e == nil {
		t.Fatal("expected an enrichment despite the empty union")
	}
	if e.Signals != nil {
		t.Errorf("expected no values, got %v", e.Signals)
	}
	if want := "violated: eventually(nothing) [core: eventually unmet]"; e.EnrichedReason != want {
		t.Errorf("EnrichedReason = %q, want %q", e.EnrichedReason, want)
	}
}

// endStreamOf is an end-of-stream response carrying the entries as written.
func endStreamOf(entries ...string) aletheia.MockResponse {
	return aletheia.Respond(`{"status":"complete","results":[` + strings.Join(entries, ",") + `],"warnings":[]}`)
}

// A holding entry ahead of a failing one is passed over, not the end of the
// walk: the failing entry after it is still enriched.
func TestEndStream_AHoldingEntryDoesNotEndTheWalk(t *testing.T) {
	c, _ := startedClientWith(t, twoSignalProperties(),
		aletheia.Respond(ack),
		endStreamOf(`{"type":"property","property_index":0,"status":"holds"}`,
			`{"type":"property","property_index":1,"status":"fails","timestamp":1000,"reason":"eventually unmet"}`),
		extractionOf("SigB", 7),
	)
	sendOn(t, c, 0x100, 0)

	results := mustEndStream(t, c, 2)
	if results[0].Enrichment != nil {
		t.Errorf("the holding entry was enriched: %+v", results[0].Enrichment)
	}
	wantOneSignal(t, results[1], "SigB", 7)
}

// The stream.ended record counts the failing and the unresolved verdicts.
func TestEndStream_TheEndedRecordCountsTheVerdicts(t *testing.T) {
	var buf bytes.Buffer
	logger := aletheia.WithLogger(slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelInfo})))
	properties := append(twoSignalProperties(), aletheia.Eventually{Inner: gt("SigC", 1)}, aletheia.Eventually{Inner: gt("SigD", 1)})
	c, _ := startedClientOpts(t, properties, []aletheia.MockResponse{
		endStreamOf(`{"type":"property","property_index":0,"status":"fails","timestamp":1000,"reason":"a"}`,
			`{"type":"property","property_index":1,"status":"unresolved","reason":"b"}`,
			`{"type":"property","property_index":2,"status":"fails","timestamp":1000,"reason":"c"}`,
			`{"type":"property","property_index":3,"status":"holds"}`),
	}, logger)

	mustEndStream(t, c, 4)
	var ended string
	for line := range strings.SplitSeq(buf.String(), "\n") {
		if strings.Contains(line, "msg=stream.ended") {
			ended = line
		}
	}
	for _, want := range []string{"numResults=4", "numFails=2", "numUnresolved=1"} {
		if !strings.Contains(ended, want) {
			t.Errorf("stream.ended record %q lacks %s", ended, want)
		}
	}
}
