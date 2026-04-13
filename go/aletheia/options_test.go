package aletheia_test

import (
	"bytes"
	"log/slog"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

func TestWithLogger(t *testing.T) {
	var buf bytes.Buffer
	logger := slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelDebug}))

	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"holds"}]
		}`), // EndStream
	)
	c, err := aletheia.NewClient(mock, aletheia.WithLogger(logger))
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

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data); err != nil {
		t.Fatal(err)
	}

	if _, err := c.EndStream(); err != nil {
		t.Fatal(err)
	}

	output := buf.String()
	for _, event := range []string{"properties.set", "stream.started", "frame.processed", "stream.ended"} {
		if !strings.Contains(output, event) {
			t.Errorf("expected log event %q in output, got:\n%s", event, output)
		}
	}
}

func TestWithLogger_Enrichment(t *testing.T) {
	var buf bytes.Buffer
	logger := slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelDebug}))

	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		// SendFrame → violation
		aletheia.Respond(`{"status":"fails","type":"property","property_index":0,"timestamp":5000,"reason":"Atomic: predicate failed"}`),
		// Extraction for enrichment
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`),
		aletheia.Respond(`{
			"status":"complete",
			"results":[{"property_index":0,"status":"fails","timestamp":5000,"reason":"Atomic: predicate failed"}]
		}`), // EndStream
		// EOS extraction
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`),
	)
	c, err := aletheia.NewClient(mock, aletheia.WithLogger(logger))
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

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0xFF, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 5000}, sid, dlc8(), data); err != nil {
		t.Fatal(err)
	}

	if _, err := c.EndStream(); err != nil {
		t.Fatal(err)
	}

	output := buf.String()
	for _, event := range []string{"cache.miss", "frame.processed"} {
		if !strings.Contains(output, event) {
			t.Errorf("expected log event %q in output, got:\n%s", event, output)
		}
	}
	if !strings.Contains(output, "response=violation") {
		t.Errorf("expected 'response=violation' in log output, got:\n%s", output)
	}
}

func TestWithoutLogger(t *testing.T) {
	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		aletheia.Respond(`{"status":"ack"}`),     // SendFrame
	)
	// No WithLogger — should not panic.
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

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	if _, err := c.SendFrame(aletheia.Timestamp{Microseconds: 1000}, sid, dlc8(), data); err != nil {
		t.Fatal(err)
	}
}

func TestWithLogger_ExtractionError(t *testing.T) {
	var buf bytes.Buffer
	logger := slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelDebug}))

	mock := aletheia.NewMockBackend(
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
		// SendFrame → violation
		aletheia.Respond(`{"status":"fails","type":"property","property_index":0,"timestamp":5000,"reason":"test"}`),
		// Extraction fails with protocol error
		aletheia.Respond(`{"status":"error","message":"no DBC loaded"}`),
	)
	c, err := aletheia.NewClient(mock, aletheia.WithLogger(logger))
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

	sid, _ := aletheia.NewStandardID(0x123)
	data := aletheia.FramePayload{0, 0, 0, 0, 0, 0, 0, 0}
	resp, err := c.SendFrame(aletheia.Timestamp{Microseconds: 5000}, sid, dlc8(), data)
	if err != nil {
		t.Fatal(err)
	}
	// Violation still returned despite extraction failure
	if _, ok := resp.(aletheia.Violation); !ok {
		t.Fatalf("expected Violation, got %T", resp)
	}

	output := buf.String()
	// extractSignalsLocked should log the specific error (parse_failed because the
	// error response is valid JSON but has status "error")
	if !strings.Contains(output, "extraction.parse_failed") {
		t.Errorf("expected 'extraction.parse_failed' in log output, got:\n%s", output)
	}
	// extractSignalValues should log the nil-result
	if !strings.Contains(output, "enrichment.extraction_failed") {
		t.Errorf("expected 'enrichment.extraction_failed' in log output, got:\n%s", output)
	}
}
