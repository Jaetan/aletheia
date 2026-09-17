// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"context"
	"errors"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// ctx is for the tests that do not exercise cancellation; one that does
// makes its own, so that what it cancels is its own call.
var ctx = context.Background()

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

// startedClientOpts is a client over a mock that has answered SetProperties
// and StartStream and holds the given responses for what follows, with the
// properties installed and the options applied. It closes when the test ends.
func startedClientOpts(t *testing.T, properties []aletheia.Formula, responses []aletheia.MockResponse, opts ...aletheia.ClientOption) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	queue := append([]aletheia.MockResponse{
		aletheia.Respond(`{"status":"success"}`), // SetProperties
		aletheia.Respond(`{"status":"success"}`), // StartStream
	}, responses...)
	mock := aletheia.NewMockBackend(queue...)
	c, err := aletheia.NewClient(mock, opts...)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = c.Close() })
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
