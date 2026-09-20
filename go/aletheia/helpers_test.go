// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"context"
	"errors"
	"fmt"
	"strings"
	"testing"
	"time"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// The helpers the tests outside the package share. internal_test_helpers_test.go
// carries the same two for the tests inside it, the two test packages being
// compiled separately: one copy would have to be exported from the package
// under test, and the only difference between them is how the error type is
// spelled from each side.

// bounded is the context a test hands the client: a call the client answers
// takes milliseconds, so a deadline of two seconds turns a hang, such as a lock
// left held by an earlier call, into a failure of this test rather than of
// the whole binary. A test that exercises cancellation makes its own.
func bounded(t *testing.T) context.Context {
	t.Helper()
	ctx, cancel := context.WithTimeout(t.Context(), 2*time.Second)
	t.Cleanup(cancel)
	return ctx
}

// closeWithin closes the client, failing the test rather than hanging it
// when Close cannot take the lock within two seconds: Close waits for the lock with no
// context, by design, so a lock an earlier call left held would otherwise
// block the whole binary.
func closeWithin(t *testing.T, c *aletheia.Client) error {
	t.Helper()
	done := make(chan error, 1)
	go func() { done <- c.Close() }()
	select {
	case err := <-done:
		return err
	case <-time.After(2 * time.Second):
		t.Fatal("Close did not return within two seconds: the client lock is still held")
		return nil
	}
}

// requireErrorContains holds that the failure is the binding's own error type,
// through whatever wraps it, and that its message carries the substring.
func requireErrorContains(t *testing.T, err error, substr string) {
	t.Helper()
	if err == nil {
		t.Fatal("expected error, got nil")
	}
	var e *aletheia.Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if !strings.Contains(err.Error(), substr) {
		t.Errorf("expected error containing %q, got: %v", substr, err)
	}
}

// dlc8 is the eight-byte length every fixture here uses. The constructor
// cannot refuse it, eight being a valid length, so the error is dropped.
func dlc8() aletheia.DLC {
	d, _ := aletheia.NewDLC(8)
	return d
}

// testDBC is the fixture the tests parse and validate: one message carrying
// one unsigned little-endian speed signal, a tenth of a unit per count.
func testDBC() aletheia.DBCDefinition {
	sid, _ := aletheia.NewStandardID(0x123)
	return aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
			{
				ID:     sid,
				Name:   "EngineData",
				DLC:    dlc8(),
				Sender: "ECU",
				Signals: []aletheia.DBCSignal{
					{
						Name:      "Speed",
						StartBit:  0,
						BitLength: 16,
						ByteOrder: aletheia.LittleEndian,
						IsSigned:  false,
						Factor:    aletheia.Rational{Numerator: 1, Denominator: 10},
						Offset:    aletheia.Rational{Numerator: 0, Denominator: 1},
						Minimum:   aletheia.Rational{Numerator: 0, Denominator: 1},
						Maximum:   aletheia.Rational{Numerator: 300, Denominator: 1},
						Unit:      "km/h",
						Presence:  aletheia.AlwaysPresent{},
					},
				},
			},
		},
	}
}

// These four build what a test hands the mock, and need no kernel, so they sit
// here rather than in the files that do.
func lt(sig string, v int64) aletheia.Formula {
	return aletheia.Atomic{Predicate: aletheia.LessThan{Signal: aletheia.SignalName(sig), Value: aletheia.IntRational(v)}}
}

func gt(sig string, v int64) aletheia.Formula {
	return aletheia.Atomic{Predicate: aletheia.GreaterThan{Signal: aletheia.SignalName(sig), Value: aletheia.IntRational(v)}}
}

// extractionOf is a successful extraction response carrying the named integer values.
func extractionOf(values ...any) aletheia.MockResponse {
	parts := make([]string, 0, len(values)/2)
	for i := 0; i+1 < len(values); i += 2 {
		parts = append(parts, fmt.Sprintf(`{"name":%q,"value":%d}`, values[i], values[i+1]))
	}
	return aletheia.Respond(`{"status":"success","values":[` + strings.Join(parts, ",") + `],"errors":[],"absent":[]}`)
}

// sendFrame sends one frame on the identifier these tests enrich.
func sendFrame(t *testing.T, c *aletheia.Client, ts int64, data ...byte) aletheia.FrameResponse {
	t.Helper()
	return sendOn(t, c, 0x123, ts, data...)
}

// mockClient is a client over a mock holding the given responses, closed when
// the test ends.
func mockClient(t *testing.T, responses ...aletheia.MockResponse) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	mock := aletheia.NewMockBackend(responses...)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = closeWithin(t, c) })
	return c, mock
}

func standardID(t *testing.T, v uint16) aletheia.StandardID {
	t.Helper()
	sid, err := aletheia.NewStandardID(v)
	if err != nil {
		t.Fatal(err)
	}
	return sid
}

// requireKind asserts err is an *aletheia.Error of the kind.
func requireKind(t *testing.T, err error, kind aletheia.ErrorKind) {
	t.Helper()
	if err == nil {
		t.Fatal("expected an error, got nil")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if aErr.Kind != kind {
		t.Errorf("kind: got %s, want %s: %v", aErr.Kind, kind, err)
	}
}

// formatDBCResponse is a success response to FormatDBC carrying one message.
func formatDBCResponse(message string) string {
	return `{"status":"success","dbc":{"version":"","messages":[` + message + `]}}`
}

// oneSignalMessage is a standard-ID message carrying one signal.
func oneSignalMessage(signal string) string {
	return `{"id":100,"extended":false,"name":"Msg","dlc":8,"sender":"ECU","signals":[` + signal + `]}`
}

// standardFrame is a frame of the eight-byte length on a standard identifier,
// carrying the payload given or eight zero bytes.
func standardFrame(t *testing.T, id uint16, ts int64, data ...byte) aletheia.Frame {
	t.Helper()
	if len(data) == 0 {
		data = make([]byte, 8)
	}
	sid, err := aletheia.NewStandardID(id)
	if err != nil {
		t.Fatalf("NewStandardID(%#x): %v", id, err)
	}
	return aletheia.Frame{
		Timestamp: aletheia.Timestamp{Microseconds: ts},
		ID:        sid,
		DLC:       dlc8(),
		Data:      aletheia.FramePayload(data),
	}
}

// sendOn sends one such frame and answers what the kernel said about it.
func sendOn(t *testing.T, c *aletheia.Client, id uint16, ts int64, data ...byte) aletheia.FrameResponse {
	t.Helper()
	ctx := bounded(t)
	f := standardFrame(t, id, ts, data...)
	resp, err := c.SendFrame(ctx, f.Timestamp, f.ID, f.DLC, f.Data, nil, nil)
	if err != nil {
		t.Fatalf("SendFrame on %#x: %v", id, err)
	}
	return resp
}

// speedBelow is the property most of these tests install.
func speedBelow(limit int64) aletheia.Formula {
	return aletheia.Always{Inner: aletheia.Atomic{
		Predicate: aletheia.LessThan{Signal: "Speed", Value: aletheia.IntRational(limit)}}}
}

// startedClientOpts is a client over a mock that has answered SetProperties
// and StartStream and holds the given responses for what follows, with the
// properties installed and the options applied. It closes when the test ends.
func startedClientOpts(t *testing.T, properties []aletheia.Formula, responses []aletheia.MockResponse, opts ...aletheia.ClientOption) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	ctx := bounded(t)
	queue := append([]aletheia.MockResponse{
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
	}, responses...)
	mock := aletheia.NewMockBackend(queue...)
	c, err := aletheia.NewClient(mock, opts...)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = closeWithin(t, c) })
	if err := c.SetProperties(ctx, properties); err != nil {
		t.Fatal(err)
	}
	if err := c.StartStream(ctx); err != nil {
		t.Fatal(err)
	}
	return c, mock
}

// startedClientWith is that client with no option.
func startedClientWith(t *testing.T, properties []aletheia.Formula, responses ...aletheia.MockResponse) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	return startedClientOpts(t, properties, responses)
}
