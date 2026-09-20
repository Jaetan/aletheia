//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"errors"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

const ack = `{"status":"ack"}`

// startedBatchClient is startedClientWith over the one property Speed below the limit.
func startedBatchClient(t *testing.T, limit int64, responses ...aletheia.MockResponse) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	return startedClientWith(t, []aletheia.Formula{speedBelow(limit)}, responses...)
}

// frameAt is a frame on the identifier these tests batch on.
func frameAt(t *testing.T, ts int64, data ...byte) aletheia.Frame {
	t.Helper()
	return standardFrame(t, 0x100, ts, data...)
}

// sentinelCount is how many binary frame sends the mock recorded.
func sentinelCount(mock *aletheia.MockBackend) int {
	n := 0
	for _, in := range mock.Inputs() {
		if in == "<binary:sendFrame>" {
			n++
		}
	}
	return n
}

func TestSendFrames_AllAck(t *testing.T) {
	ctx := bounded(t)
	c, _ := startedBatchClient(t, 300, aletheia.Respond(ack), aletheia.Respond(ack), aletheia.Respond(ack))
	frames := []aletheia.Frame{
		frameAt(t, 1000, 0, 0, 0, 0, 0, 0, 0, 0),
		frameAt(t, 2000, 1, 0, 0, 0, 0, 0, 0, 0),
		frameAt(t, 3000, 2, 0, 0, 0, 0, 0, 0, 0),
	}

	results, err := c.SendFrames(ctx, frames)
	if err != nil {
		t.Fatalf("SendFrames: %v", err)
	}
	if len(results) != 3 {
		t.Fatalf("expected 3 results, got %d", len(results))
	}
	for i, r := range results {
		if _, ok := r.(aletheia.Ack); !ok {
			t.Errorf("result[%d]: expected Ack, got %T", i, r)
		}
	}
}

func TestSendFrames_WithViolation(t *testing.T) {
	ctx := bounded(t)
	c, _ := startedBatchClient(t, 220,
		aletheia.Respond(ack), // frame 1
		aletheia.Respond(`{
			"type":"property_batch",
			"results":[{
				"type":"property",
				"status":"fails",
				"property_index":0,
				"timestamp":2000,
				"reason":"Speed >= 220"
			}]
		}`), // frame 2, the violation
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`), // the extraction that enriches it
		aletheia.Respond(ack), // frame 3
	)
	frames := []aletheia.Frame{
		frameAt(t, 1000, 0, 0, 0, 0, 0, 0, 0, 0),
		frameAt(t, 2000, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0),
		frameAt(t, 3000, 0, 0, 0, 0, 0, 0, 0, 0),
	}

	results, err := c.SendFrames(ctx, frames)
	if err != nil {
		t.Fatalf("SendFrames: %v", err)
	}
	if len(results) != 3 {
		t.Fatalf("expected 3 results, got %d", len(results))
	}
	if _, ok := results[0].(aletheia.Ack); !ok {
		t.Errorf("result[0]: expected Ack, got %T", results[0])
	}
	b, ok := results[1].(aletheia.PropertyBatch)
	if !ok {
		t.Fatalf("result[1]: expected PropertyBatch, got %T", results[1])
	}
	v := b.FirstViolation()
	if v == nil {
		t.Fatalf("expected violation in batch, got %+v", b)
	}
	if v.PropertyIndex != 0 {
		t.Errorf("violation property index: got %d, want 0", v.PropertyIndex)
	}
	if v.Enrichment == nil {
		t.Fatal("expected enrichment on batch violation")
	}
	if _, ok := results[2].(aletheia.Ack); !ok {
		t.Errorf("result[2]: expected Ack, got %T", results[2])
	}
}

// A frame that fails validation stops the batch before the backend sees it,
// and the frames sent before it are returned.
func TestSendFrames_StopsOnValidationError(t *testing.T) {
	ctx := bounded(t)
	c, mock := startedBatchClient(t, 300, aletheia.Respond(ack))
	frames := []aletheia.Frame{
		frameAt(t, 1000, 0, 0, 0, 0, 0, 0, 0, 0),
		frameAt(t, 2000, 0, 0, 0), // 3 bytes against DLC 8
		frameAt(t, 3000, 0, 0, 0, 0, 0, 0, 0, 0),
	}

	results, err := c.SendFrames(ctx, frames)
	requireErrorContains(t, err, "payload length")
	requireErrorContains(t, err, "frame 1")
	if len(results) != 1 {
		t.Errorf("expected 1 partial result, got %d", len(results))
	}
	if n := sentinelCount(mock); n != 1 {
		t.Errorf("expected 1 frame sent before the failure, got %d", n)
	}
}

// A backend failure on one frame stops the batch: the error names the frame
// and wraps the backend's, the committed prefix is returned, and no later
// frame is sent.
func TestSendFrames_StopsOnBackendError(t *testing.T) {
	ctx := bounded(t)
	boom := aletheia.NewValidationError("the backend refused the frame")
	c, mock := startedBatchClient(t, 300, aletheia.Respond(ack), aletheia.RespondErr(boom))
	frames := []aletheia.Frame{
		frameAt(t, 1000, 0, 0, 0, 0, 0, 0, 0, 0),
		frameAt(t, 2000, 0, 0, 0, 0, 0, 0, 0, 0),
		frameAt(t, 3000, 0, 0, 0, 0, 0, 0, 0, 0),
	}

	results, err := c.SendFrames(ctx, frames)
	if !errors.Is(err, boom) {
		t.Fatalf("expected the backend error to be wrapped, got %v", err)
	}
	requireErrorContains(t, err, "frame 1")
	if len(results) != 1 {
		t.Errorf("expected 1 partial result, got %d", len(results))
	}
	if n := sentinelCount(mock); n != 2 {
		t.Errorf("expected 2 frames sent (the failing one included), got %d", n)
	}
}

func TestSendFrames_Empty(t *testing.T) {
	ctx := bounded(t)
	c, _ := startedBatchClient(t, 300)

	results, err := c.SendFrames(ctx, nil)
	if err != nil {
		t.Fatalf("SendFrames(nil): %v", err)
	}
	if len(results) != 0 {
		t.Errorf("expected 0 results, got %d", len(results))
	}
}

func TestSendFrames_NegativeTimestamp(t *testing.T) {
	ctx := bounded(t)
	c, mock := startedBatchClient(t, 300)
	frames := []aletheia.Frame{frameAt(t, -1, 0, 0, 0, 0, 0, 0, 0, 0)}

	results, err := c.SendFrames(ctx, frames)
	if err == nil {
		t.Fatal("expected error for negative timestamp")
	}
	if len(results) != 0 {
		t.Errorf("expected 0 results before error, got %d", len(results))
	}
	if n := sentinelCount(mock); n != 0 {
		t.Errorf("expected no frame sent, got %d", n)
	}
}

func TestSendFrames_AfterClose(t *testing.T) {
	ctx := bounded(t)
	c, err := aletheia.NewClient(aletheia.NewMockBackend())
	if err != nil {
		t.Fatal(err)
	}
	if err := closeWithin(t, c); err != nil {
		t.Fatal(err)
	}

	_, err = c.SendFrames(ctx, []aletheia.Frame{frameAt(t, 1000, 0, 0, 0, 0, 0, 0, 0, 0)})
	requireErrorContains(t, err, "closed")
}
