// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"slices"
	"testing"
	"unsafe"
)

// lockCheckingBackend is a routingBackend that records, at every entry, whether
// the client's lock is held, and counts the sessions it is asked to close.
type lockCheckingBackend struct {
	routingBackend
	client   *Client
	unlocked []int // the ordinals of calls entered without the lock
	closes   int
}

func (b *lockCheckingBackend) Close(_ unsafe.Pointer) {
	b.closes++
	if len(b.client.lockCh) != 1 {
		b.unlocked = append(b.unlocked, -1)
	}
}

// The client is safe to share between goroutines because every call reaches
// the backend holding the client's lock, and touches the client's state only
// between taking the lock and releasing it. That discipline is what this
// holds, call by call, rather than racing goroutines against each other and
// hoping a scheduler shows a fault: each exported call is made once, it must
// reach the backend, and it must find the lock held there. Close frees the
// session once however often it is called, and with the lock held.
func TestClient_EveryCallReachesTheBackendHoldingTheLock(t *testing.T) {
	ctx := t.Context()
	parsed := RespondParseDBC(testDefinition())
	if parsed.Err != nil {
		t.Fatalf("RespondParseDBC: %v", parsed.Err)
	}
	backend := &lockCheckingBackend{}
	backend.hook = func(n int) (string, error) {
		if len(backend.client.lockCh) != 1 {
			backend.unlocked = append(backend.unlocked, n)
		}
		if n == 1 {
			return parsed.JSON, nil
		}
		return `{"status":"success"}`, nil
	}
	c, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	backend.client = c

	id, dlc := testDefinition().Messages[0].ID, testDefinition().Messages[0].DLC
	frame := Frame{Timestamp: Timestamp{Microseconds: 1}, ID: id, DLC: dlc, Data: make(FramePayload, dlc.ToBytes())}
	speed := []SignalValue{{Name: "Speed", Value: IntRational(1)}}
	checks := []CheckResult{CheckSignal("Speed").NeverExceeds(IntRational(220))}
	calls := []struct {
		name string
		call func()
	}{
		{"ParseDBC", func() { _, _ = c.ParseDBC(ctx, testDefinition()) }},
		{"ParseDBCText", func() { _, _ = c.ParseDBCText(ctx, "VERSION \"\"\n") }},
		{"ValidateDBC", func() { _, _ = c.ValidateDBC(ctx, testDefinition()) }},
		{"FormatDBC", func() { _, _ = c.FormatDBC(ctx) }},
		{"FormatDBCText", func() { _, _ = c.FormatDBCText(ctx, testDefinition()) }},
		{"ExtractSignals", func() { _, _ = c.ExtractSignals(ctx, id, dlc, frame.Data) }},
		{"BuildFrame", func() { _, _ = c.BuildFrame(ctx, id, dlc, speed) }},
		{"UpdateFrame", func() { _, _ = c.UpdateFrame(ctx, id, dlc, frame.Data, speed) }},
		{"SetProperties", func() { _ = c.SetProperties(ctx, nil) }},
		{"AddChecks", func() { _ = c.AddChecks(ctx, checks) }},
		{"StartStream", func() { _ = c.StartStream(ctx) }},
		{"SendFrame", func() { _, _ = c.SendFrame(ctx, frame.Timestamp, id, dlc, frame.Data, nil, nil) }},
		{"SendFrames", func() { _, _ = c.SendFrames(ctx, []Frame{frame}) }},
		{"SendFramesSeq", func() {
			for _, err := range c.SendFramesSeq(ctx, slices.Values([]Frame{frame})) {
				_ = err
			}
		}},
		{"SendError", func() { _ = c.SendError(ctx, frame.Timestamp) }},
		{"SendRemote", func() { _ = c.SendRemote(ctx, frame.Timestamp, id) }},
		{"EndStream", func() { _, _ = c.EndStream(ctx) }},
	}
	for _, tc := range calls {
		before := backend.callCount()
		tc.call()
		if backend.callCount() == before {
			t.Errorf("%s did not reach the backend, so its lock was not checked", tc.name)
		}
	}
	if len(backend.unlocked) != 0 {
		t.Errorf("calls entered the backend without the client's lock, by ordinal: %v", backend.unlocked)
	}

	for range 3 {
		if err := c.Close(); err != nil {
			t.Errorf("Close: %v", err)
		}
	}
	if backend.closes != 1 {
		t.Errorf("the session was freed %d times, want once", backend.closes)
	}
	if len(backend.unlocked) != 0 {
		t.Errorf("Close freed the session without the client's lock")
	}
}
