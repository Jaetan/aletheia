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

// ctx is the default context for tests that don't exercise cancellation.
// Tests that DO exercise cancellation create their own context.WithCancel
// or context.WithTimeout in-test.
var ctx = context.Background()

// requireErrorContains asserts err is a non-nil *aletheia.Error whose message
// contains substr. Uses errors.As for proper unwrapping.
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

// dlc8 creates a DLC with value 8 for convenience in tests.
func dlc8() aletheia.DLC {
	d, _ := aletheia.NewDLC(8)
	return d
}

// testDBC returns a minimal DBC definition for testing.
func testDBC() aletheia.DBCDefinition {
	sid, _ := aletheia.NewStandardID(0x123)
	dlc, _ := aletheia.NewDLC(8)
	return aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
			{
				ID:     sid,
				Name:   "EngineData",
				DLC:    dlc,
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

// startedClientOpts returns a client over a mock that has already answered
// SetProperties and StartStream and holds the given responses for what
// follows, with the properties installed and the options applied. The client
// is closed when the test ends.
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

// startedClientWith is startedClientOpts with no client option.
func startedClientWith(t *testing.T, properties []aletheia.Formula, responses ...aletheia.MockResponse) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	return startedClientOpts(t, properties, responses)
}
