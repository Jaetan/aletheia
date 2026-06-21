// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"context"
	"errors"
	"reflect"
	"slices"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// seqTestFrames is the canonical three-frame batch used across the lazy tests.
func seqTestFrames() []aletheia.Frame {
	sid, _ := aletheia.NewStandardID(0x100)
	return []aletheia.Frame{
		{Timestamp: aletheia.Timestamp{Microseconds: 1000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
		{Timestamp: aletheia.Timestamp{Microseconds: 2000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{1, 0, 0, 0, 0, 0, 0, 0}},
		{Timestamp: aletheia.Timestamp{Microseconds: 3000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{2, 0, 0, 0, 0, 0, 0, 0}},
	}
}

// seqStreamingClient builds a mock-backed client already past SetProperties +
// StartStream; `frameResponses` are queued for the subsequent frame sends.
func seqStreamingClient(t *testing.T, frameResponses ...aletheia.MockResponse) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	responses := append([]aletheia.MockResponse{
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
	}, frameResponses...)
	mock := aletheia.NewMockBackend(responses...)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	if err := c.SetProperties(ctx, []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.RationalFromFloat(300)}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatal(err)
	}
	return c, mock
}

func countSentinel(inputs []string, want string) int {
	n := 0
	for _, in := range inputs {
		if in == want {
			n++
		}
	}
	return n
}

func TestSendFramesSeq_AllAck(t *testing.T) {
	c, mock := seqStreamingClient(t,
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"ack"}`),
	)
	defer c.Close()

	var results []aletheia.FrameResponse
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(seqTestFrames())) {
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		results = append(results, resp)
	}

	if len(results) != 3 {
		t.Fatalf("expected 3 results, got %d", len(results))
	}
	for i, r := range results {
		if _, ok := r.(aletheia.Ack); !ok {
			t.Errorf("result[%d]: expected Ack, got %T", i, r)
		}
	}
	if got := countSentinel(mock.Inputs(), "<binary:sendFrame>"); got != 3 {
		t.Errorf("expected 3 frame sends, got %d", got)
	}
}

func TestSendFramesSeq_StopsOnError(t *testing.T) {
	// Frame 2 has a payload-length/DLC mismatch — a validation error before the
	// backend call. The sequence yields (nil, err) once, then ends.
	c, _ := seqStreamingClient(t, aletheia.Respond(`{"status":"ack"}`)) // only frame 1 reaches the backend
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x100)
	frames := []aletheia.Frame{
		{Timestamp: aletheia.Timestamp{Microseconds: 1000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
		{Timestamp: aletheia.Timestamp{Microseconds: 2000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0}}, // 3 bytes vs DLC 8
		{Timestamp: aletheia.Timestamp{Microseconds: 3000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
	}

	oks := 0
	var lastErr error
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(frames)) {
		if err != nil {
			lastErr = err
			break // idiomatic: stop on the first error
		}
		_ = resp
		oks++
	}

	if oks != 1 {
		t.Errorf("expected 1 ok prefix, got %d", oks)
	}
	requireErrorContains(t, lastErr, "payload length")
}

func TestSendFramesSeq_Empty(t *testing.T) {
	c, _ := seqStreamingClient(t)
	defer c.Close()

	count := 0
	for range c.SendFramesSeq(ctx, slices.Values([]aletheia.Frame(nil))) {
		count++
	}
	if count != 0 {
		t.Errorf("expected 0 iterations over an empty source, got %d", count)
	}
}

func TestSendFramesSeq_CancelPrefixCommitsOnly(t *testing.T) {
	// Break after 2 of 5 frames: the remaining 3 are never sent (commit-prefix),
	// proven by the recorded backend call count (deterministic, no sleeps).
	c, mock := seqStreamingClient(t,
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"ack"}`),
	)
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x100)
	var frames []aletheia.Frame
	for i := 0; i < 5; i++ {
		frames = append(frames, aletheia.Frame{
			Timestamp: aletheia.Timestamp{Microseconds: int64(i+1) * 1000},
			ID:        sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0},
		})
	}

	got := 0
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(frames)) {
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		_ = resp
		got++
		if got == 2 {
			break
		}
	}

	if got != 2 {
		t.Errorf("expected to consume 2 frames, got %d", got)
	}
	if sent := countSentinel(mock.Inputs(), "<binary:sendFrame>"); sent != 2 {
		t.Errorf("commit-prefix: expected exactly 2 frames sent to backend, got %d", sent)
	}
}

func TestSendFramesSeq_MatchesEager(t *testing.T) {
	// Equivalence: the same frames through SendFrames (eager) and SendFramesSeq
	// (lazy) must produce identical per-frame responses AND the identical backend
	// call log — the guarantee that the two loop wrappers cannot drift.
	mkResponses := func() []aletheia.MockResponse {
		return []aletheia.MockResponse{
			aletheia.Respond(`{"status":"ack"}`),
			aletheia.Respond(`{"status":"ack"}`),
			aletheia.Respond(`{"status":"ack"}`),
		}
	}

	ce, me := seqStreamingClient(t, mkResponses()...)
	defer ce.Close()
	eager, err := ce.SendFrames(ctx, seqTestFrames())
	if err != nil {
		t.Fatalf("eager: %v", err)
	}

	cl, ml := seqStreamingClient(t, mkResponses()...)
	defer cl.Close()
	var lazy []aletheia.FrameResponse
	for resp, err := range cl.SendFramesSeq(ctx, slices.Values(seqTestFrames())) {
		if err != nil {
			t.Fatalf("lazy: %v", err)
		}
		lazy = append(lazy, resp)
	}

	if !reflect.DeepEqual(eager, lazy) {
		t.Errorf("eager vs lazy responses differ:\n eager %+v\n lazy  %+v", eager, lazy)
	}
	if !slices.Equal(me.Inputs(), ml.Inputs()) {
		t.Errorf("backend call log differs:\n eager %v\n lazy  %v", me.Inputs(), ml.Inputs())
	}
}

func TestSendFramesSeq_CtxCancelMidStream(t *testing.T) {
	// The ctx-fired path (distinct from stopping by breaking the range): once
	// ctx is cancelled, the next frame's acquire returns the wrapped ctx error,
	// yielded as the terminal (nil, err); the remaining frames are not sent.
	c, mock := seqStreamingClient(t,
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"ack"}`),
	)
	defer c.Close()

	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	oks := 0
	var termErr error
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(seqTestFrames())) {
		if err != nil {
			termErr = err
			break
		}
		_ = resp
		oks++
		cancel() // cancel after the first committed frame
	}

	if oks != 1 {
		t.Errorf("expected 1 committed frame before cancellation, got %d", oks)
	}
	if !errors.Is(termErr, context.Canceled) {
		t.Errorf("expected a context.Canceled terminal error, got %v", termErr)
	}
	if sent := countSentinel(mock.Inputs(), "<binary:sendFrame>"); sent != 1 {
		t.Errorf("expected exactly 1 frame sent, got %d", sent)
	}
}

func TestSendFramesSeq_AfterClose(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	c.Close()

	sid, _ := aletheia.NewStandardID(0x100)
	frames := []aletheia.Frame{
		{Timestamp: aletheia.Timestamp{Microseconds: 1000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
	}

	var sawErr error
	count := 0
	for resp, err := range c.SendFramesSeq(ctx, slices.Values(frames)) {
		count++
		if err != nil {
			sawErr = err
			break
		}
		_ = resp
	}

	requireErrorContains(t, sawErr, "closed")
	if count != 1 {
		t.Errorf("expected exactly one (nil, err) yield on a closed client, got %d", count)
	}
}
