//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"bytes"
	"log/slog"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// What the client logs, and that it runs the same way with no logger at all.

// speedUnder220 is the property every case here installs.
func speedUnder220() []aletheia.Formula {
	return []aletheia.Formula{
		aletheia.Always{Inner: aletheia.Atomic{
			Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(220)},
		}},
	}
}

// loggedClient is a started client writing to a buffer the caller reads.
func loggedClient(t *testing.T, responses ...aletheia.MockResponse) (*aletheia.Client, *bytes.Buffer) {
	t.Helper()
	var buf bytes.Buffer
	logger := slog.New(slog.NewTextHandler(&buf, &slog.HandlerOptions{Level: slog.LevelDebug}))
	c, _ := startedClientOpts(t, speedUnder220(), responses, aletheia.WithLogger(logger))
	return c, &buf
}

// requireLogged holds that each event was written.
func requireLogged(t *testing.T, output string, events ...string) {
	t.Helper()
	for _, event := range events {
		if !strings.Contains(output, event) {
			t.Errorf("the log does not carry %q:\n%s", event, output)
		}
	}
}

// zeroPayload is eight bytes of nothing, which no property here reads.
var zeroPayload = []byte{0, 0, 0, 0, 0, 0, 0, 0}

// A stream from end to end writes one event per step.
func TestWithLogger_StreamLifecycle(t *testing.T) {
	c, buf := loggedClient(t,
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"complete","results":[{"property_index":0,"status":"holds"}]}`),
	)
	sendFrame(t, c, 1000, zeroPayload...)
	if _, err := c.EndStream(ctx); err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	requireLogged(t, buf.String(), "properties.set", "stream.started", "frame.processed", "stream.ended")
}

// A violation is logged as one, and the extraction it drives reports that the
// signal was not in the cache.
func TestWithLogger_Enrichment(t *testing.T) {
	c, buf := loggedClient(t,
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":5000,"reason":"Atomic: predicate failed"}]}`),
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`),
		aletheia.Respond(`{"status":"complete","results":[{"property_index":0,"status":"fails","timestamp":5000,"reason":"Atomic: predicate failed"}]}`),
		aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":250}],"errors":[],"absent":[]}`),
	)
	sendFrame(t, c, 5000, 0xFF, 0, 0, 0, 0, 0, 0, 0)
	if _, err := c.EndStream(ctx); err != nil {
		t.Fatalf("EndStream: %v", err)
	}
	output := buf.String()
	requireLogged(t, output, "cache.miss", "frame.processed")
	if !strings.Contains(output, "response=violation") {
		t.Errorf("the frame was not logged as a violation:\n%s", output)
	}
}

// An extraction that fails is logged twice, once where it failed and once
// where the enrichment gave up, and the violation still reaches the caller.
func TestWithLogger_ExtractionError(t *testing.T) {
	c, buf := loggedClient(t,
		aletheia.Respond(`{"type":"property_batch","results":[{"type":"property","status":"fails","property_index":0,"timestamp":5000,"reason":"test"}]}`),
		aletheia.Respond(`{"status":"error","code":"handler_no_dbc","message":"no DBC loaded"}`),
	)
	resp := sendFrame(t, c, 5000, zeroPayload...)
	if _, ok := resp.(aletheia.PropertyBatch); !ok {
		t.Fatalf("the frame answered %T, want the violation despite the failed extraction", resp)
	}
	requireLogged(t, buf.String(), "extraction.parse_failed", "enrichment.extraction_failed")
}

// With no logger the same stream runs, every logging site being a no-op
// rather than a call on nothing.
func TestWithoutLogger(t *testing.T) {
	c, _ := startedClientOpts(t, speedUnder220(), []aletheia.MockResponse{
		aletheia.Respond(`{"status":"ack"}`),
		aletheia.Respond(`{"status":"complete","results":[{"property_index":0,"status":"holds"}]}`),
	})
	sendFrame(t, c, 1000, zeroPayload...)
	if _, err := c.EndStream(ctx); err != nil {
		t.Fatalf("EndStream: %v", err)
	}
}
