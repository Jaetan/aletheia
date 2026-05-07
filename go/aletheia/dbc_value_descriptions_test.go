//go:build cgo && linux

// SPDX-License-Identifier: BSD-2-Clause

// Track E — VAL_ value descriptions on DbcSignal.ValueDescriptions and the
// matching CHECK 23 (UnknownValueDescriptionTarget) emitted by parse_dbc_text
// when a VAL_ line points at a (message-id, signal-name) pair not declared in
// BO_ / SG_.
//
// These are real-FFI tests in the same vein as TestDBCCorpusParity — VAL_
// promotion is end-to-end across the Agda parser + formatter + validator, so a
// MockBackend would only verify the wire shape, not the round-trip semantics.

package aletheia

import (
	"strings"
	"testing"
)

// newFFIClient wires up a real-FFI Client for tests that need round-trip
// fidelity. Mirrors the setup in TestDBCCorpusParity.
func newFFIClient(t *testing.T) *Client {
	t.Helper()
	lib := findFFILibForParityTest()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}
	backend, err := NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	client, err := NewClient(backend)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	t.Cleanup(func() {
		if err := client.Close(); err != nil {
			t.Errorf("Close: %v", err)
		}
	})
	return client
}

// TestParseDBCText_ValueDescriptionsRoundTrip parses a fixture that carries a
// non-empty VAL_ line, asserts the entries land on
// DbcSignal.ValueDescriptions, then re-emits via FormatDBCText and confirms the
// VAL_ block is part of the textual output.
func TestParseDBCText_ValueDescriptionsRoundTrip(t *testing.T) {
	client := newFFIClient(t)

	const text = `VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 300 Transmission: 8 ECU
 SG_ EngineState : 8|2@1+ (1,0) [0|3] "" Vector__XXX

VAL_ 300 EngineState 0 "Off" 1 "Cranking" 2 "Running" 3 "Stall" ;
`

	parsed, err := client.ParseDBCText(ctx, text)
	if err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	if len(parsed.DBC.Messages) != 1 || len(parsed.DBC.Messages[0].Signals) != 1 {
		t.Fatalf("unexpected DBC shape: %+v", parsed.DBC)
	}
	sig := parsed.DBC.Messages[0].Signals[0]
	if len(sig.ValueDescriptions) != 4 {
		t.Fatalf("expected 4 value descriptions, got %d: %+v",
			len(sig.ValueDescriptions), sig.ValueDescriptions)
	}
	want := []DbcValueEntry{
		{Value: 0, Description: "Off"},
		{Value: 1, Description: "Cranking"},
		{Value: 2, Description: "Running"},
		{Value: 3, Description: "Stall"},
	}
	for i, w := range want {
		if sig.ValueDescriptions[i] != w {
			t.Errorf("entry %d: got %+v, want %+v", i, sig.ValueDescriptions[i], w)
		}
	}

	out, err := client.FormatDBCText(ctx, parsed.DBC)
	if err != nil {
		t.Fatalf("FormatDBCText: %v", err)
	}
	const wantLine = `VAL_ 300 EngineState 0 "Off" 1 "Cranking" 2 "Running" 3 "Stall" ;`
	if !strings.Contains(out, wantLine) {
		t.Errorf("expected VAL_ block in formatted output, got:\n%s", out)
	}
}

// TestParseDBCText_UnknownValueDescriptionTargetWarning checks that CHECK 23
// fires when a VAL_ line refers to a (message-id, signal-name) pair not
// declared in BO_ / SG_. The unresolved entry survives on
// DBC.UnresolvedValueDescriptions; validateDBCFull walks that list and emits
// `unknown_value_description_target` warnings, surfaced on
// ParsedDBC.Warnings.
func TestParseDBCText_UnknownValueDescriptionTargetWarning(t *testing.T) {
	client := newFFIClient(t)

	const text = `VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 Engine: 8 ECU
 SG_ Rpm : 0|16@1+ (1,0) [0|8000] "rpm" Vector__XXX

VAL_ 999 GhostSignal 0 "Off" 1 "On" ;
`

	parsed, err := client.ParseDBCText(ctx, text)
	if err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}

	var hit bool
	for _, w := range parsed.Warnings {
		if w.Code == IssueUnknownValueDescriptionTarget {
			hit = true
			break
		}
	}
	if !hit {
		t.Errorf("expected unknown_value_description_target warning, got %+v",
			parsed.Warnings)
	}
}
