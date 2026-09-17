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
		parts = append(parts, fmt.Sprintf(`{"property_index":%d,"status":"fails","timestamp":1000,"reason":"eventually unmet"}`, i))
	}
	return aletheia.Respond(`{"status":"complete","results":[` + strings.Join(parts, ",") + `]}`)
}

// endStreamHolds is an end-of-stream response satisfying the given properties.
func endStreamHolds(indices ...int) aletheia.MockResponse {
	parts := make([]string, 0, len(indices))
	for _, i := range indices {
		parts = append(parts, fmt.Sprintf(`{"property_index":%d,"status":"holds"}`, i))
	}
	return aletheia.Respond(`{"status":"complete","results":[` + strings.Join(parts, ",") + `]}`)
}

// warnLog is a client option collecting warnings into the buffer it returns.
func warnLog() (aletheia.ClientOption, *bytes.Buffer) {
	var buf bytes.Buffer
	return aletheia.WithLogger(slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelWarn}))), &buf
}

// mustEndStream ends the stream and returns its verdicts.
func mustEndStream(t *testing.T, c *aletheia.Client, want int) []aletheia.PropertyResult {
	t.Helper()
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

// Two failing properties over one frame whose extraction fails: the frame is
// attempted once and warned about once, where a walk per property would warn
// twice, and both entries still carry the fallback enrichment.
func TestEndStream_FailedExtractionWarnsOncePerFrame(t *testing.T) {
	logger, logged := warnLog()
	c, mock := startedClientOpts(t, twoSignalProperties(), []aletheia.MockResponse{
		aletheia.Respond(ack),
		endStreamFails(0, 1),
		aletheia.Respond(`{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}`),
	}, logger)
	sendOn(t, c, 0x100, 0)

	results := mustEndStream(t, c, 2)
	if got := extractCalls(mock); got != 1 {
		t.Errorf("expected 1 extraction attempt for the one frame, got %d", got)
	}
	if got := strings.Count(logged.String(), "enrichment.extraction_failed"); got != 1 {
		t.Errorf("expected 1 extraction_failed warning, got %d in:\n%s", got, logged.String())
	}
	for i, pr := range results {
		if pr.Enrichment == nil {
			t.Fatalf("result %d: expected the fallback enrichment", i)
		}
		if pr.Enrichment.Signals != nil {
			t.Errorf("result %d: expected no values after a failed extraction, got %v", i, pr.Enrichment.Signals)
		}
		if !strings.HasPrefix(pr.Enrichment.EnrichedReason, "violated: ") {
			t.Errorf("result %d: EnrichedReason = %q, want the formula fallback", i, pr.Enrichment.EnrichedReason)
		}
	}
}

// A verdict naming a property that does not exist is warned about once and
// left unenriched, and it drives no extraction of its own; the valid entry
// beside it is enriched.
func TestEndStream_OOBIndexExcludedValidEntryStillEnriched(t *testing.T) {
	logger, logged := warnLog()
	c, mock := startedClientOpts(t, twoSignalProperties()[:1], []aletheia.MockResponse{
		aletheia.Respond(ack),
		endStreamFails(0, 3),
		extractionOf("SigA", 5),
	}, logger)
	sendOn(t, c, 0x100, 0)

	results := mustEndStream(t, c, 2)
	out := logged.String()
	if got := strings.Count(out, "enrichment.property_index_oob"); got != 1 {
		t.Errorf("expected 1 property_index_oob warning, got %d in:\n%s", got, out)
	}
	if !strings.Contains(out, "index=3") || !strings.Contains(out, "count=1") {
		t.Errorf("expected the warning to name index 3 against 1 property, got:\n%s", out)
	}
	if got := extractCalls(mock); got != 1 {
		t.Errorf("expected 1 extraction, got %d", got)
	}
	wantOneSignal(t, results[0], "SigA", 5)
	if results[1].Enrichment != nil {
		t.Errorf("the out-of-bounds entry was enriched: %+v", results[1].Enrichment)
	}
}

// With no frame ever sent there is nothing to extract, and the failing entry
// still carries an enrichment with the fallback reason and the core's.
//
// This is also where the skip of the extraction pass over an empty union of
// wanted signals is observable, since that union cannot be emptied through
// the public surface: every serializable formula has an atomic leaf and the
// signal collector keeps even an empty name. Inverting the skip's condition
// would zero the extractions the other tests here count.
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
