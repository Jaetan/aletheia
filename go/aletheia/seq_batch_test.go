//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"context"
	"errors"
	"reflect"
	"slices"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// Sending frames as a sequence: what the caller gets, what reaches the
// backend, and where each stops.

// seqFrames is n frames a fifth of a millisecond apart, each carrying its own
// index so that no two are the same bytes.
func seqFrames(n int) []aletheia.Frame {
	sid, _ := aletheia.NewStandardID(0x100)
	frames := make([]aletheia.Frame, 0, n)
	for i := range n {
		frames = append(frames, aletheia.Frame{
			Timestamp: aletheia.Timestamp{Microseconds: int64(i+1) * 1000},
			ID:        sid, DLC: dlc8(),
			Data: aletheia.FramePayload{byte(i), 0, 0, 0, 0, 0, 0, 0},
		})
	}
	return frames
}

// seqStreamingClient is the shared started client, under a property no frame
// here breaks, with the given answers queued for the frames.
func seqStreamingClient(t *testing.T, frameResponses ...aletheia.MockResponse) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	return startedClientWith(t, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{
			Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(300)},
		}},
	}, frameResponses...)
}

// acks is n canned acknowledgements.
func acks(n int) []aletheia.MockResponse {
	out := make([]aletheia.MockResponse, 0, n)
	for range n {
		out = append(out, aletheia.Respond(`{"status":"ack"}`))
	}
	return out
}

// framesSent is how many frames reached the backend.
func framesSent(mock *aletheia.MockBackend) int {
	n := 0
	for _, in := range mock.Inputs() {
		if in == "<binary:sendFrame>" {
			n++
		}
	}
	return n
}

// Every frame is answered, in order, and every one reaches the backend.
func TestSendFramesSeq_AllAck(t *testing.T) {
	c, mock := seqStreamingClient(t, acks(3)...)
	var results []aletheia.FrameResponse
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(seqFrames(3))) {
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		results = append(results, resp)
	}
	if len(results) != 3 {
		t.Fatalf("got %d answers, want 3", len(results))
	}
	for i, r := range results {
		if _, ok := r.(aletheia.Ack); !ok {
			t.Errorf("answer %d is %T, want an acknowledgement", i, r)
		}
	}
	if got := framesSent(mock); got != 3 {
		t.Errorf("%d frames reached the backend, want 3", got)
	}
}

// A frame the client refuses ends the sequence: the frames before it were
// answered, and nothing after it is sent. The second frame carries fewer bytes
// than its length declares, which is refused before the backend is reached.
func TestSendFramesSeq_StopsOnError(t *testing.T) {
	c, mock := seqStreamingClient(t, acks(1)...)
	frames := seqFrames(3)
	frames[1].Data = aletheia.FramePayload{0, 0, 0}

	answered := 0
	var lastErr error
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(frames)) {
		if err != nil {
			lastErr = err
			break
		}
		_ = resp
		answered++
	}

	if answered != 1 {
		t.Errorf("%d frames were answered before the refusal, want 1", answered)
	}
	if got := framesSent(mock); got != 1 {
		t.Errorf("%d frames reached the backend, want 1", got)
	}
	requireErrorContains(t, lastErr, "payload length")
}

// A sequence with no frames yields nothing.
func TestSendFramesSeq_Empty(t *testing.T) {
	c, _ := seqStreamingClient(t)
	count := 0
	for range c.SendFramesSeq(ctx, slices.Values([]aletheia.Frame(nil))) {
		count++
	}
	if count != 0 {
		t.Errorf("an empty sequence yielded %d times", count)
	}
}

// A caller that stops reading stops the sending: the frames it did not ask
// for never reach the backend, which the recorded calls show without waiting
// on anything.
func TestSendFramesSeq_StoppingEarlySendsNoMore(t *testing.T) {
	c, mock := seqStreamingClient(t, acks(5)...)
	read := 0
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(seqFrames(5))) {
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		_ = resp
		read++
		if read == 2 {
			break
		}
	}
	if read != 2 {
		t.Errorf("read %d frames, want 2", read)
	}
	if sent := framesSent(mock); sent != 2 {
		t.Errorf("%d frames reached the backend after stopping at two", sent)
	}
}

// The two ways of sending a batch answer alike and call the backend alike, so
// neither can drift from the other.
func TestSendFramesSeq_MatchesTheEagerBatch(t *testing.T) {
	ce, me := seqStreamingClient(t, acks(3)...)
	eager, err := ce.SendFrames(ctx, seqFrames(3))
	if err != nil {
		t.Fatalf("the eager batch: %v", err)
	}

	cl, ml := seqStreamingClient(t, acks(3)...)
	var lazy []aletheia.FrameResponse
	for resp, err := range cl.SendFramesSeq(ctx, slices.Values(seqFrames(3))) {
		if err != nil {
			t.Fatalf("the sequence: %v", err)
		}
		lazy = append(lazy, resp)
	}

	if !reflect.DeepEqual(eager, lazy) {
		t.Errorf("the answers differ:\n eager %+v\n sequence %+v", eager, lazy)
	}
	if !slices.Equal(me.Inputs(), ml.Inputs()) {
		t.Errorf("the calls differ:\n eager %v\n sequence %v", me.Inputs(), ml.Inputs())
	}
}

// A cancelled context ends the sequence from the other side: the frame after
// the cancellation is refused rather than sent, and the refusal carries the
// cancellation.
func TestSendFramesSeq_CtxCancelMidStream(t *testing.T) {
	c, mock := seqStreamingClient(t, acks(3)...)
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	answered := 0
	var termErr error
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(seqFrames(3))) {
		if err != nil {
			termErr = err
			break
		}
		_ = resp
		answered++
		cancel() // after the first frame has been answered
	}

	if answered != 1 {
		t.Errorf("%d frames were answered before the cancellation, want 1", answered)
	}
	if !errors.Is(termErr, context.Canceled) {
		t.Errorf("the sequence ended with %v, want the cancellation", termErr)
	}
	if sent := framesSent(mock); sent != 1 {
		t.Errorf("%d frames reached the backend, want 1", sent)
	}
}

// A sequence on a closed client yields one refusal and stops.
func TestSendFramesSeq_AfterClose(t *testing.T) {
	c, err := aletheia.NewClient(aletheia.NewMockBackend())
	if err != nil {
		t.Fatal(err)
	}
	if err := c.Close(); err != nil {
		t.Fatalf("Close: %v", err)
	}

	var sawErr error
	count := 0
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(seqFrames(1))) {
		count++
		if err != nil {
			sawErr = err
			break
		}
		_ = resp
	}

	requireErrorContains(t, sawErr, "closed")
	if count != 1 {
		t.Errorf("the sequence yielded %d times on a closed client, want once", count)
	}
}
