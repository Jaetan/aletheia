package aletheia_test

import (
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

func TestSendFrames_AllAck(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // Frame 1
		aletheia.Respond(`{"status":"ack"}`),     // Frame 2
		aletheia.Respond(`{"status":"ack"}`),     // Frame 3
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
	frames := []aletheia.Frame{
		{Timestamp: aletheia.Timestamp{Microseconds: 1000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
		{Timestamp: aletheia.Timestamp{Microseconds: 2000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{1, 0, 0, 0, 0, 0, 0, 0}},
		{Timestamp: aletheia.Timestamp{Microseconds: 3000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{2, 0, 0, 0, 0, 0, 0, 0}},
	}

	results, err := c.SendFrames(frames)
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
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // Frame 1
		aletheia.Respond(`{
			"status":"fails",
			"type":"property",
			"property_index":0,
			"timestamp":2000,
			"reason":"Speed >= 220"
		}`), // Frame 2 — violation
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`), // extraction for enrichment
		aletheia.Respond(`{"status":"ack"}`), // Frame 3
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
	frames := []aletheia.Frame{
		{Timestamp: aletheia.Timestamp{Microseconds: 1000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
		{Timestamp: aletheia.Timestamp{Microseconds: 2000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0xFF, 0xFF, 0, 0, 0, 0, 0, 0}},
		{Timestamp: aletheia.Timestamp{Microseconds: 3000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
	}

	results, err := c.SendFrames(frames)
	if err != nil {
		t.Fatalf("SendFrames: %v", err)
	}
	if len(results) != 3 {
		t.Fatalf("expected 3 results, got %d", len(results))
	}
	if _, ok := results[0].(aletheia.Ack); !ok {
		t.Errorf("result[0]: expected Ack, got %T", results[0])
	}
	v, ok := results[1].(aletheia.Violation)
	if !ok {
		t.Fatalf("result[1]: expected Violation, got %T", results[1])
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

func TestSendFrames_StopsOnError(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // Frame 1
		// Frame 2 has invalid DLC/payload — validation error before backend call
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
	frames := []aletheia.Frame{
		{Timestamp: aletheia.Timestamp{Microseconds: 1000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
		{Timestamp: aletheia.Timestamp{Microseconds: 2000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0}}, // 3 bytes vs DLC 8
		{Timestamp: aletheia.Timestamp{Microseconds: 3000}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
	}

	results, err := c.SendFrames(frames)
	requireErrorContains(t, err, "payload length")
	// First frame succeeded before the error.
	if len(results) != 1 {
		t.Errorf("expected 1 partial result, got %d", len(results))
	}
}

func TestSendFrames_Empty(t *testing.T) {
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
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 300}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	results, err := c.SendFrames(nil)
	if err != nil {
		t.Fatalf("SendFrames(nil): %v", err)
	}
	if len(results) != 0 {
		t.Errorf("expected 0 results, got %d", len(results))
	}
}

func TestSendFrames_NegativeTimestamp(t *testing.T) {
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
		aletheia.Always{Inner: aletheia.Atomic{Predicate: aletheia.LessThan{Signal: "Speed", Value: 300}}},
	}); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(); err != nil {
		t.Fatal(err)
	}

	sid, _ := aletheia.NewStandardID(0x100)
	frames := []aletheia.Frame{
		{Timestamp: aletheia.Timestamp{Microseconds: -1}, ID: sid, DLC: dlc8(), Data: aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}},
	}

	results, err := c.SendFrames(frames)
	if err == nil {
		t.Fatal("expected error for negative timestamp")
	}
	if len(results) != 0 {
		t.Errorf("expected 0 results before error, got %d", len(results))
	}
}

func TestSendFrames_AfterClose(t *testing.T) {
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

	_, err = c.SendFrames(frames)
	requireErrorContains(t, err, "closed")
}
