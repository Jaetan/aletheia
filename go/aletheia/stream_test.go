package aletheia_test

import (
	"errors"
	"strings"
	"sync"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

func TestStreamingLTL_NoViolation(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"holds"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: 200,
		}}},
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}

	err = c.StartStream()
	if err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0x64, 0, 0, 0, 0, 0, 0, 0}

	resp1, err := c.SendFrame(aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data)
	if err != nil {
		t.Fatalf("SendFrame 1: %v", err)
	}
	if _, ok := resp1.(aletheia.Ack); !ok {
		t.Errorf("expected Ack, got %T", resp1)
	}

	resp2, err := c.SendFrame(aletheia.Timestamp{Microseconds: 2000}, sid, dlc8(), data)
	if err != nil {
		t.Fatalf("SendFrame 2: %v", err)
	}
	if _, ok := resp2.(aletheia.Ack); !ok {
		t.Errorf("expected Ack, got %T", resp2)
	}

	result, err := c.EndStream()
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Holds {
		t.Errorf("expected Holds, got %s", result.Results[0].Verdict)
	}
}

func TestStreamingLTL_Violation(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"fails",
			"type":"property",
			"property_index":0,
			"timestamp":5000,
			"reason":"Speed >= 200"
		}`), // SendFrame — violation
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`), // extraction for enrichment
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","timestamp":5000,"reason":"Speed >= 200"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Never(aletheia.GreaterThanOrEqual{Signal: "Speed", Value: 200}),
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}

	err = c.StartStream()
	if err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0xFF, 0xFF, 0, 0, 0, 0, 0, 0}

	resp, err := c.SendFrame(aletheia.Timestamp{Microseconds: 5000}, sid, dlc8(), data)
	if err != nil {
		t.Fatalf("SendFrame: %v", err)
	}
	v, ok := resp.(aletheia.Violation)
	if !ok {
		t.Fatalf("expected Violation, got %T", resp)
	}
	if v.PropertyIndex != 0 {
		t.Errorf("expected property 0, got %d", v.PropertyIndex)
	}
	if v.Timestamp.Microseconds != 5000 {
		t.Errorf("expected ts=5000, got %d", v.Timestamp.Microseconds)
	}
	if v.Reason != "Speed >= 200" {
		t.Errorf("expected reason 'Speed >= 200', got %q", v.Reason)
	}

	result, err := c.EndStream()
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if result.Results[0].Verdict != aletheia.Fails {
		t.Errorf("expected Fails, got %s", result.Results[0].Verdict)
	}
	if result.Results[0].Timestamp == nil {
		t.Fatal("expected non-nil timestamp")
	}
	if result.Results[0].Timestamp.Microseconds != 5000 {
		t.Errorf("expected ts=5000, got %d", result.Results[0].Timestamp.Microseconds)
	}
}

func TestViolation_CoreReason(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"fails",
			"type":"property",
			"property_index":0,
			"timestamp":5000,
			"reason":"MetricEventually: window expired"
		}`), // SendFrame — violation
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":50}],"errors":[],"absent":[]}`), // extraction
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","timestamp":5000,"reason":"MetricEventually: window expired"}]
		}`), // EndStream
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":50}],"errors":[],"absent":[]}`), // EOS extraction
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.MetricEventually{
			Bound: aletheia.TimeBound{Microseconds: 5_000_000},
			Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: "Speed", Value: 100}},
		},
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	resp, err := c.SendFrame(aletheia.Timestamp{Microseconds: 5000}, sid, dlc8(), data)
	if err != nil {
		t.Fatal(err)
	}

	v, ok := resp.(aletheia.Violation)
	if !ok {
		t.Fatalf("expected Violation, got %T", resp)
	}
	if v.Enrichment == nil {
		t.Fatal("expected non-nil Enrichment")
	}
	if v.Enrichment.CoreReason != "MetricEventually: window expired" {
		t.Errorf("CoreReason = %q, want %q", v.Enrichment.CoreReason, "MetricEventually: window expired")
	}
	if !strings.Contains(v.Enrichment.EnrichedReason, "[core: MetricEventually: window expired]") {
		t.Errorf("EnrichedReason = %q, want core reason appended", v.Enrichment.EnrichedReason)
	}

	// End-of-stream verdict should also carry the core reason.
	sr, err := c.EndStream()
	if err != nil {
		t.Fatal(err)
	}
	pr := sr.Results[0]
	if pr.Enrichment == nil {
		t.Fatal("expected non-nil EOS Enrichment")
	}
	if pr.Enrichment.CoreReason != "MetricEventually: window expired" {
		t.Errorf("EOS CoreReason = %q, want %q", pr.Enrichment.CoreReason, "MetricEventually: window expired")
	}
	if !strings.Contains(pr.Enrichment.EnrichedReason, "[core: MetricEventually: window expired]") {
		t.Errorf("EOS EnrichedReason = %q, want core reason appended", pr.Enrichment.EnrichedReason)
	}
}

func TestViolation_EmptyCoreReason(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"fails",
			"type":"property",
			"property_index":0,
			"timestamp":5000
		}`), // SendFrame — violation with no reason field
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`), // extraction
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}},
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0xFF, 0, 0, 0, 0, 0, 0, 0}
	resp, err := c.SendFrame(aletheia.Timestamp{Microseconds: 5000}, sid, dlc8(), data)
	if err != nil {
		t.Fatal(err)
	}

	v, ok := resp.(aletheia.Violation)
	if !ok {
		t.Fatalf("expected Violation, got %T", resp)
	}
	if v.Enrichment == nil {
		t.Fatal("expected non-nil Enrichment")
	}
	if v.Enrichment.CoreReason != "" {
		t.Errorf("CoreReason = %q, want empty", v.Enrichment.CoreReason)
	}
	// EnrichedReason should not contain [core: ] when core reason is empty
	if strings.Contains(v.Enrichment.EnrichedReason, "[core:") {
		t.Errorf("EnrichedReason = %q, should not contain [core:] when empty", v.Enrichment.EnrichedReason)
	}
}

func TestMetricFormulas(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.AlwaysWithin(
			aletheia.TimeBound{Microseconds: 5_000_000},
			aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 200}},
		),
		aletheia.EventuallyWithin(
			aletheia.TimeBound{Microseconds: 1_000_000},
			aletheia.Atomic{Predicate: aletheia.Equals{Signal: "Mode", Value: 1}},
		),
	})
	if err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
}

func TestEndStream_TimestampParseError(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{"status":"success"}`),
		aletheia.Respond(`{
			"status":"complete",
			"results":[{
				"property_index":0,
				"status":"holds",
				"reason":"",
				"timestamp":"not_a_number"
			}]
		}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 300}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	_, err = c.EndStream()
	requireErrorContains(t, err, "invalid timestamp")
}

func TestSendError_Ack(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendError
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 300}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	if err := c.SendError(aletheia.Timestamp{Microseconds: 1000}); err != nil {
		t.Fatalf("SendError: %v", err)
	}

	// Verify the mock saw the serialized error event as its third input.
	inputs := mock.Inputs()
	if len(inputs) != 3 {
		t.Fatalf("expected 3 inputs, got %d", len(inputs))
	}
	if !strings.Contains(inputs[2], `"type":"error"`) || !strings.Contains(inputs[2], `"timestamp":1000`) {
		t.Errorf("expected error event in third input, got: %s", inputs[2])
	}
}

func TestSendError_NegativeTimestamp(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SendError(aletheia.Timestamp{Microseconds: -1})
	requireErrorContains(t, err, "timestamp must be non-negative")
}

func TestSendRemote_Ack(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendRemote
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 300}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	if err := c.SendRemote(aletheia.Timestamp{Microseconds: 1000}, sid); err != nil {
		t.Fatalf("SendRemote: %v", err)
	}

	// Verify the mock saw the serialized remote event as its third input.
	inputs := mock.Inputs()
	if len(inputs) != 3 {
		t.Fatalf("expected 3 inputs, got %d", len(inputs))
	}
	if !strings.Contains(inputs[2], `"type":"remote"`) || !strings.Contains(inputs[2], `"id":256`) {
		t.Errorf("expected remote event in third input, got: %s", inputs[2])
	}
}

func TestSendRemote_NegativeTimestamp(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	sid, _ := aletheia.NewStandardID(0x100)
	err = c.SendRemote(aletheia.Timestamp{Microseconds: -1}, sid)
	requireErrorContains(t, err, "timestamp must be non-negative")
}

func TestSendError_AfterClose(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	c.Close()

	err = c.SendError(aletheia.Timestamp{Microseconds: 1000})
	requireErrorContains(t, err, "closed")
}

func TestSendError_RejectsSuccessStatus(t *testing.T) {
	// Trace events always resolve to Response.Ack in Agda, so "success" must
	// not be accepted for send_error.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"success"}`), // SendError — wrong status
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	if err := c.SetProperties(nil); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}
	err = c.SendError(aletheia.Timestamp{Microseconds: 1000})
	requireErrorContains(t, err, `unexpected status: "success"`)
}

func TestSendRemote_RejectsSuccessStatus(t *testing.T) {
	// Trace events always resolve to Response.Ack in Agda, so "success" must
	// not be accepted for send_remote.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"success"}`), // SendRemote — wrong status
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	if err := c.SetProperties(nil); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}
	sid, _ := aletheia.NewStandardID(0x100)
	err = c.SendRemote(aletheia.Timestamp{Microseconds: 1000}, sid)
	requireErrorContains(t, err, `unexpected status: "success"`)
}

func TestConcurrentSendFrame(t *testing.T) {
	const n = 10
	responses := make([]aletheia.MockResponse, 0, n+2)
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // SetProperties
	responses = append(responses, aletheia.Respond(`{"status":"success"}`)) // StartStream
	for i := 0; i < n; i++ {
		responses = append(responses, aletheia.Respond(`{"status":"ack"}`))
	}

	mock := aletheia.NewMockBackend(responses...)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 300}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	var wg sync.WaitGroup
	for i := 0; i < n; i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()
			sid, _ := aletheia.NewStandardID(uint16(0x100 + idx))
			data := aletheia.FramePayload{byte(idx), 0, 0, 0, 0, 0, 0, 0}
			_, _ = c.SendFrame(aletheia.Timestamp{Microseconds: int64(idx * 1000)}, sid, dlc8(), data)
		}(i)
	}
	wg.Wait()
}

func TestSendFrame_NegativeTimestamp(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	_, err = c.SendFrame(aletheia.Timestamp{Microseconds: -1}, sid, dlc8(), data)
	requireErrorContains(t, err, "timestamp must be non-negative")
}

// TestSendFrame_NonMonotonicTimestamp verifies the Go binding correctly parses
// the JSON error response that Agda's handleDataFrame produces when a frame
// regresses in time. The monotonicity check lives in Agda (see
// FrameProcessor/Properties.agda PROPERTY 28); the Go binding's job is to
// surface the error code to the caller.
func TestSendFrame_NonMonotonicTimestamp(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame @ 5000
		aletheia.Respond(`{"status":"error","code":"handler_non_monotonic_timestamp","message":"DataFrame: non-monotonic timestamp: 4999 µs < previous 5000 µs (metric LTL operators require monotonic timestamps)"}`),
		aletheia.Respond(`{"status":"ack"}`), // SendFrame @ 5000 (=, accepted)
		aletheia.Respond(`{"status":"ack"}`), // SendFrame @ 6000
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 500}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{10, 0, 0, 0, 0, 0, 0, 0}

	// First frame at t=5000 — accepted.
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 5000}, sid, dlc8(), data); err != nil {
		t.Fatalf("first SendFrame: %v", err)
	}

	// Regressing to t=4999 — rejected by Agda; binding surfaces the coded error.
	_, err = c.SendFrame(aletheia.Timestamp{Microseconds: 4999}, sid, dlc8(), data)
	if err == nil {
		t.Fatal("expected error for backward timestamp")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T", err)
	}
	if aErr.Code != aletheia.CodeHandlerNonMonotonicTimestamp {
		t.Errorf("expected code %q, got %q", aletheia.CodeHandlerNonMonotonicTimestamp, aErr.Code)
	}
	if aErr.Kind != aletheia.ErrProtocol {
		t.Errorf("expected ErrProtocol, got %s", aErr.Kind)
	}
	requireErrorContains(t, err, "non-monotonic")

	// Same-timestamp frames (≥, not >) should still be accepted.
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 5000}, sid, dlc8(), data); err != nil {
		t.Fatalf("equal-timestamp SendFrame: %v", err)
	}

	// Anchor unchanged after rejection — forward frame still works.
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 6000}, sid, dlc8(), data); err != nil {
		t.Fatalf("forward SendFrame: %v", err)
	}
}

func TestSendFrame_PayloadDLCMismatch(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	shortData := aletheia.FramePayload{0, 0, 0, 0} // 4 bytes vs DLC 8
	_, err = c.SendFrame(aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), shortData)
	requireErrorContains(t, err, "payload length")
}

func TestSetProperties_NegativeTimeBound(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.MetricAlways{
			Bound: aletheia.TimeBound{Microseconds: -1000},
			Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}},
		},
	})
	requireErrorContains(t, err, "negative time bound")
}

func TestSetProperties_NegativeDelta(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	// Negative delta is valid — directional semantics (curr - prev <= delta)
	err = c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.ChangedBy{Signal: "Speed", Delta: -5}}},
	})
	if err != nil {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestSetProperties_NegativeTolerance(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.StableWithin{Signal: "Speed", Tolerance: -2}}},
	})
	requireErrorContains(t, err, "negative tolerance")
}

// --- Group Q: Out-of-order streaming tests ---

func TestSendFrame_WithoutStartStream(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		// SendFrame without StartStream — Agda core responds with error
		aletheia.Respond(`{"status":"error","message":"no active stream"}`),
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}},
	}); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	_, err = c.SendFrame(aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data)
	if err == nil {
		t.Fatal("expected error for SendFrame without StartStream")
	}
}

func TestEndStream_WithoutStartStream(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`),                     // SetProperties
		aletheia.Respond(`{"status":"error","message":"no stream"}`), // EndStream without StartStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}},
	}); err != nil {
		t.Fatal(err)
	}

	_, err = c.EndStream()
	if err == nil {
		t.Fatal("expected error for EndStream without StartStream")
	}
}

func TestConsecutiveStartStream(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream (1st)
		aletheia.Respond(`{"status":"success"}`), // StartStream (2nd)
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}},
	}); err != nil {
		t.Fatal(err)
	}

	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}
}

// --- Group R6-I: PropertyIndex out-of-bounds tests ---

func TestSendFrame_PropertyIndexOutOfBounds(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties (1 property)
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"fails",
			"type":"property",
			"property_index":5,
			"timestamp":1000,
			"reason":"out of bounds"
		}`), // SendFrame — violation with OOB index
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	resp, err := c.SendFrame(aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data)
	if err != nil {
		t.Fatalf("SendFrame: %v", err)
	}
	v, ok := resp.(aletheia.Violation)
	if !ok {
		t.Fatalf("expected Violation, got %T", resp)
	}
	if v.PropertyIndex != 5 {
		t.Errorf("expected property_index=5, got %d", v.PropertyIndex)
	}
	// OOB index → enrichment should be nil (graceful degradation).
	if v.Enrichment != nil {
		t.Errorf("expected nil Enrichment for OOB property index, got %+v", v.Enrichment)
	}
}

func TestStreamingLTL_Unresolved(t *testing.T) {
	// Atomic predicate whose signal was never observed finalizes to
	// Unresolved (three-valued Kleene Unknown) rather than Fails.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame (unrelated frame)
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Atomic: predicate never resolved at end of stream"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "UnobservedSignal", Value: 100,
		}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream()
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Unresolved {
		t.Errorf("expected Unresolved, got %s", result.Results[0].Verdict)
	}
	if !strings.Contains(result.Results[0].Reason, "never resolved") {
		t.Errorf("expected reason to mention 'never resolved', got %q", result.Results[0].Reason)
	}
}

func TestEndStream_PropertyIndexOutOfBounds(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties (1 property)
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":5,"status":"fails","timestamp":1000,"reason":"out of bounds"}]
		}`), // EndStream — result with OOB index
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 220}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	result, err := c.EndStream()
	if err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	if len(result.Results) != 1 {
		t.Fatalf("expected 1 result, got %d", len(result.Results))
	}
	if result.Results[0].Verdict != aletheia.Fails {
		t.Errorf("expected Fails, got %s", result.Results[0].Verdict)
	}
	// OOB index → enrichment should be nil (graceful degradation).
	if result.Results[0].Enrichment != nil {
		t.Errorf("expected nil Enrichment for OOB property index, got %+v", result.Results[0].Enrichment)
	}
}

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
// Go uses MockBackend (not real FFI) because the Go binding's surface is JSON
// marshaling — feedback_cross_binding_test_placement.md records this as valid
// parity. These tests verify the JSON → Verdict → PropertyResult pipeline and
// the enrichment branch in Client.EndStream.

func TestEOS_AlwaysNeverObserved_ManyFrames(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 1
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 2
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 3
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 4
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 5
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Atomic: predicate never resolved at end of stream"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: 100,
		}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	for i := range 5 {
		ts := aletheia.Timestamp{Microseconds: int64(i) * 1000}
		if _, err := c.SendFrame(ts, sid, dlc8(), data); err != nil {
			t.Fatalf("SendFrame %d: %v", i, err)
		}
	}

	result, err := c.EndStream()
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
	// A single frame gives changed_by(0) no prior observation to compare
	// against, so its inner Atomic finalizes to Unsure. Under Kleene K3 the
	// negation stays Unsure and the Always absorption leaves an
	// And (Not Atomic) (Always _) which reduces via Unsure ∧ Holds = Unsure.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"ChangedBy: single-frame trace"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Not{Inner: aletheia.Atomic{
			Predicate: aletheia.ChangedBy{Signal: "Speed", Delta: 0},
		}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{10, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream()
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
	// Regression guard: pre-Path-G this collapsed to Fails via the
	// Or φ (Eventually ψ) → Eventually ψ absorption. Path G guards that
	// rewrite with finalizesFails φ = true, so a bare Atomic (finalizeL =
	// Unsure) no longer triggers it — the Or persists and finalizes via
	// Unsure ∨ Fails = Unsure.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 1
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 2
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 3
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 4
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame 5
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Atomic: predicate never resolved at end of stream"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
			Signal: "Speed", Value: 10,
		}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	for i := range 5 {
		ts := aletheia.Timestamp{Microseconds: int64(i) * 1000}
		if _, err := c.SendFrame(ts, sid, dlc8(), data); err != nil {
			t.Fatalf("SendFrame %d: %v", i, err)
		}
	}

	result, err := c.EndStream()
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
	// Contrast with the N ≥ 1 case above. On the empty trace, finalizeL is
	// applied directly to Eventually _ which returns Fails — liveness
	// operators do not get three-valued absorption on the empty trace.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","reason":"Eventually: never satisfied"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
			Signal: "Speed", Value: 10,
		}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	result, err := c.EndStream()
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
	// Standard LTLf vacuous truth: G φ on the empty trace holds regardless
	// of whether φ's signal would be observable. Distinguishes the
	// empty-trace finalization path (direct on Always) from the non-empty
	// path (finalizeL after progression leaves an And behind).
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"holds"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: 100,
		}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	result, err := c.EndStream()
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
	// Kleene truth table: Unsure ∧ Holds = Unsure. The And combinator with
	// one Unresolved operand and one Holds operand must surface as
	// Unresolved. Verifies the JSON status mapping and the Go Verdict
	// constant roundtrip on a representative K3 conjunction case.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"And: Unsure ∧ Holds = Unsure"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.And{
			Left: aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
				Signal: "Speed", Value: 100,
			}}},
			Right: aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
				Signal: "Rpm", Value: 100,
			}}},
		},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream()
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
	// Kleene truth table: Unsure ∨ Fails = Unsure. An Or with one Unresolved
	// operand and one Fails operand must surface as Unresolved.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Or: Unsure ∨ Fails = Unsure"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Or{
			Left: aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
				Signal: "Speed", Value: 100,
			}}},
			Right: aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
				Signal: "Rpm", Value: 999999,
			}}},
		},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream()
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
	// Stream with three properties that finalize to different K3 verdicts.
	// Confirms the Go result decoder correctly parses and orders a mix of
	// Holds, Fails, and Unresolved in a single stream response.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[
				{"property_index":0,"status":"holds"},
				{"property_index":1,"status":"fails","timestamp":1000,"reason":"Eventually: never satisfied"},
				{"property_index":2,"status":"unresolved","reason":"Atomic: predicate never resolved"}
			]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: 1000,
		}}},
		aletheia.Eventually{Inner: aletheia.Atomic{Predicate: aletheia.GreaterThan{
			Signal: "Speed", Value: 999999,
		}}},
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Rpm", Value: 100,
		}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	data := aletheia.FramePayload{10, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream()
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
	// Client.EndStream runs enrichPropertyResult for Unresolved verdicts
	// (client.go case Unresolved). Verify the enrichment field is populated
	// with FormulaDesc/CoreReason for an Unresolved result, parallel to the
	// Fails enrichment path exercised by TestEndStream_Enriched.
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"unresolved","reason":"Atomic: predicate never resolved at end of stream"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	if err := c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{
			Signal: "Speed", Value: 100,
		}}},
	}); err != nil {
		t.Fatalf("SetProperties: %v", err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatalf("StartStream: %v", err)
	}

	sid, _ := aletheia.NewStandardID(0x200)
	data := aletheia.FramePayload{5, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 0}, sid, dlc8(), data); err != nil {
		t.Fatalf("SendFrame: %v", err)
	}

	result, err := c.EndStream()
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
