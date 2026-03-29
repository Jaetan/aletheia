package aletheia_test

import (
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
			"results":[{"property_index":0,"status":"satisfaction"}]
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
			"status":"violation",
			"property_index":0,
			"timestamp":5000,
			"reason":"Speed >= 200"
		}`), // SendFrame — violation
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`), // extraction for enrichment
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"violation","timestamp":5000,"reason":"Speed >= 200"}]
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
			"status":"violation",
			"property_index":0,
			"timestamp":5000,
			"reason":"MetricEventually: window expired"
		}`), // SendFrame — violation
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":50}],"errors":[],"absent":[]}`), // extraction
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"violation","timestamp":5000,"reason":"MetricEventually: window expired"}]
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
			"status":"violation",
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
				"status":"satisfaction",
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
	if err == nil {
		t.Fatal("expected error for non-numeric timestamp")
	}
	if !strings.Contains(err.Error(), "invalid timestamp") {
		t.Errorf("expected 'invalid timestamp' in error, got: %s", err)
	}
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
	if err == nil {
		t.Fatal("expected error for negative timestamp")
	}
	if !strings.Contains(err.Error(), "negative timestamp") {
		t.Errorf("unexpected error: %v", err)
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
	if err == nil {
		t.Fatal("expected error for payload/DLC mismatch")
	}
	if !strings.Contains(err.Error(), "payload length") {
		t.Errorf("unexpected error: %v", err)
	}
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
	if err == nil {
		t.Fatal("expected error for negative time bound")
	}
	if !strings.Contains(err.Error(), "negative time bound") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestSetProperties_NegativeDelta(t *testing.T) {
	mock := aletheia.NewMockBackend()
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	err = c.SetProperties([]aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.ChangedBy{Signal: "Speed", Delta: -5}}},
	})
	if err == nil {
		t.Fatal("expected error for negative delta")
	}
	if !strings.Contains(err.Error(), "negative delta") {
		t.Errorf("unexpected error: %v", err)
	}
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
			"status":"violation",
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

func TestEndStream_PropertyIndexOutOfBounds(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties (1 property)
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":5,"status":"violation","timestamp":1000,"reason":"out of bounds"}]
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
