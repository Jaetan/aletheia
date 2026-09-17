//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/v5/aletheia"
)

// Multiplexing nested three deep, against the library rather than a mock: what
// a signal selected by a signal that is itself selected does is the kernel's
// decision, and a canned answer would only show that the client relays one.

// nestedMuxDBC is one message whose signals form a chain: the mode is always
// there, the sub-mode is there when the mode is three, and the detail is there
// when the sub-mode is seven. The detail is reachable only when both hold.
func nestedMuxDBC() aletheia.DBCDefinition {
	sid, _ := aletheia.NewStandardID(0x300)
	dlc, _ := aletheia.NewDLC(8)
	under := func(multiplexor string, value aletheia.MultiplexValue) aletheia.SignalPresence {
		return aletheia.Multiplexed{
			Multiplexor:     aletheia.SignalName(multiplexor),
			MultiplexValues: []aletheia.MultiplexValue{value},
		}
	}
	byteSignal := func(name string, startBit aletheia.BitPosition, bits aletheia.BitLength,
		max int64, presence aletheia.SignalPresence) aletheia.DBCSignal {
		return aletheia.DBCSignal{
			Name: aletheia.SignalName(name), StartBit: startBit, BitLength: bits,
			ByteOrder: aletheia.LittleEndian,
			Factor:    ratOf(1, 1), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(max, 1),
			Presence: presence,
		}
	}
	return aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{{
			ID: sid, Name: "NestedMuxMessage", DLC: dlc, Sender: "ECU",
			Signals: []aletheia.DBCSignal{
				byteSignal("Mode", 0, 8, 255, aletheia.AlwaysPresent{}),
				byteSignal("SubMode", 8, 8, 255, under("Mode", 3)),
				byteSignal("Detail", 16, 16, 65535, under("SubMode", 7)),
			},
		}},
	}
}

// nestedMuxClient is a client on the library with the nested definition loaded.
func nestedMuxClient(t *testing.T) *aletheia.Client {
	t.Helper()
	backend, err := aletheia.NewFFIBackend(requireFFILib(t))
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	c, err := aletheia.NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() { _ = c.Close() })
	return c
}

// The chain loads, and the validator names only what it is: a shape with no
// single always-present master, which is a warning rather than a refusal.
func TestNestedMux_LoadsAndIsNamedAWarning(t *testing.T) {
	c := nestedMuxClient(t)
	if _, err := c.ParseDBC(ctx, nestedMuxDBC()); err != nil {
		t.Fatalf("a nested chain must load: %v", err)
	}
	result, err := c.ValidateDBC(ctx, nestedMuxDBC())
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if result.HasErrors {
		t.Errorf("a nested chain was refused rather than named: %+v", result.Issues)
	}
	if len(result.Issues) != 1 || result.Issues[0].Code != aletheia.IssueMuxMasterIncoherent ||
		result.Issues[0].Severity != aletheia.SeverityWarning {
		t.Errorf("issues = %+v, want only the incoherent-master warning", result.Issues)
	}
}

// Each link of the chain decides whether the next signal is there. With both
// selectors matching the leaf carries its value; with the inner one off the
// leaf is absent; with the outer one off the inner signal and the leaf are.
func TestNestedMux_ExtractionFollowsTheChain(t *testing.T) {
	c := nestedMuxClient(t)
	if _, err := c.ParseDBC(ctx, nestedMuxDBC()); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}
	sid, err := aletheia.NewStandardID(0x300)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	cases := map[string]struct {
		payload aletheia.FramePayload
		present map[string]int64
		absent  []aletheia.SignalName
	}{
		"both selectors match": {
			aletheia.FramePayload{0x03, 0x07, 0xCD, 0xAB, 0, 0, 0, 0},
			map[string]int64{"Mode": 3, "SubMode": 7, "Detail": 0xABCD},
			nil,
		},
		"the inner selector does not": {
			aletheia.FramePayload{0x03, 0x05, 0xCD, 0xAB, 0, 0, 0, 0},
			map[string]int64{"Mode": 3, "SubMode": 5},
			[]aletheia.SignalName{"Detail"},
		},
		"the outer selector does not": {
			aletheia.FramePayload{0x02, 0x07, 0xCD, 0xAB, 0, 0, 0, 0},
			map[string]int64{"Mode": 2},
			[]aletheia.SignalName{"SubMode", "Detail"},
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			result, err := c.ExtractSignals(ctx, sid, dlc8(), tc.payload)
			if err != nil {
				t.Fatalf("ExtractSignals: %v", err)
			}
			if len(result.Values) != len(tc.present) {
				t.Fatalf("values = %+v, want %d of them", result.Values, len(tc.present))
			}
			for signal, want := range tc.present {
				got, ok := result.Get(aletheia.SignalName(signal))
				if !ok {
					t.Errorf("%s is absent, want %d", signal, want)
					continue
				}
				if got != aletheia.IntRational(want) {
					t.Errorf("%s = %v, want %d", signal, got, want)
				}
			}
			absent := map[aletheia.SignalName]bool{}
			for _, n := range result.Absent {
				absent[n] = true
			}
			if len(result.Absent) != len(tc.absent) {
				t.Errorf("absent = %v, want %v", result.Absent, tc.absent)
			}
			for _, want := range tc.absent {
				if !absent[want] {
					t.Errorf("%s is not among the absent: %v", want, result.Absent)
				}
			}
		})
	}
}

// Two signals each selected by the other is a cycle, which the validator
// refuses: it names each signal of the cycle, and the errors flag goes up.
func TestNestedMux_CycleIsRefused(t *testing.T) {
	c := nestedMuxClient(t)
	sid, err := aletheia.NewStandardID(0x301)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	dlc, err := aletheia.NewDLC(8)
	if err != nil {
		t.Fatalf("NewDLC: %v", err)
	}
	selectedBy := func(name string, startBit aletheia.BitPosition, multiplexor string) aletheia.DBCSignal {
		return aletheia.DBCSignal{
			Name: aletheia.SignalName(name), StartBit: startBit, BitLength: 8,
			ByteOrder: aletheia.LittleEndian,
			Factor:    ratOf(1, 1), Offset: ratOf(0, 1), Minimum: ratOf(0, 1), Maximum: ratOf(255, 1),
			Presence: aletheia.Multiplexed{
				Multiplexor:     aletheia.SignalName(multiplexor),
				MultiplexValues: []aletheia.MultiplexValue{1},
			},
		}
	}
	cycle := aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{{
			ID: sid, Name: "CycleMsg", DLC: dlc, Sender: "ECU",
			Signals: []aletheia.DBCSignal{
				selectedBy("A", 0, "B"),
				selectedBy("B", 8, "A"),
			},
		}},
	}
	result, err := c.ValidateDBC(ctx, cycle)
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if !result.HasErrors {
		t.Fatalf("a cycle was not refused: %+v", result.Issues)
	}
	named := map[aletheia.SignalName]bool{}
	for _, issue := range result.Issues {
		if issue.Code == aletheia.IssueMultiplexorCycle && issue.Severity == aletheia.SeverityError {
			for _, signal := range []aletheia.SignalName{"A", "B"} {
				if strings.Contains(issue.Detail, string(signal)) {
					named[signal] = true
				}
			}
		}
	}
	for _, signal := range []aletheia.SignalName{"A", "B"} {
		if !named[signal] {
			t.Errorf("no cycle error names %s: %+v", signal, result.Issues)
		}
	}
}
