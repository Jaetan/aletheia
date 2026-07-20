//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Warning-class validator mirrors of the two round-trip-fatal-but-loads-fine
// mux shapes: a multi-value mux selector (CHECK 24, multi_value_mux_selector)
// and an incoherent mux master (CHECK 25, mux_master_incoherent).
//
// Real-FFI tests in the same vein as the CHECK 23 coverage in
// dbc_value_descriptions_test.go — the mirrors are kernel semantics (the
// validator reuses the text-round-trip deciders), so a MockBackend would only
// verify the wire shape, not that validateDBC actually names the shapes.
// Both shapes are constructible only through the JSON route (the text parser
// yields singleton-selector, single-master assignments by construction), so
// the DBCs are built as typed literals here.

package aletheia

import "testing"

// mirrorSignal builds an 8-bit little-endian unsigned signal with unit
// scaling, mirroring the defaults the Python validator tests use.
func mirrorSignal(name string, startBit uint8, presence SignalPresence) DBCSignal {
	return DBCSignal{
		Name: SignalName(name), StartBit: BitPosition(startBit), BitLength: 8,
		ByteOrder: LittleEndian, IsSigned: false,
		Factor:  Rational{Numerator: 1, Denominator: 1},
		Offset:  Rational{Numerator: 0, Denominator: 1},
		Minimum: Rational{Numerator: 0, Denominator: 1},
		Maximum: Rational{Numerator: 255, Denominator: 1},
		Unit:    "", Presence: presence,
	}
}

func mirrorDBC(t *testing.T, signals ...DBCSignal) DBCDefinition {
	t.Helper()
	sid, err := NewStandardID(0x100)
	if err != nil {
		t.Fatalf("NewStandardID: %v", err)
	}
	dlc, err := NewDLC(8)
	if err != nil {
		t.Fatalf("NewDLC: %v", err)
	}
	return DBCDefinition{
		Version: "1.0",
		Messages: []DBCMessage{{
			ID: sid, Name: "Msg1", DLC: dlc, Sender: "ECU", Signals: signals,
		}},
	}
}

// multiValueMuxDBC carries a signal multiplexed on TWO selector values —
// streams fine, but .dbc text emits only the first value, so the shape
// cannot round-trip.
func multiValueMuxDBC(t *testing.T) DBCDefinition {
	t.Helper()
	return mirrorDBC(t,
		mirrorSignal("Mux", 0, AlwaysPresent{}),
		mirrorSignal("Payload", 8, Multiplexed{
			Multiplexor:     "Mux",
			MultiplexValues: []MultiplexValue{1, 2},
		}),
	)
}

// splitMasterDBC carries slaves under TWO Always masters — each named master
// exists (no error-class check trips), but .dbc text keeps a single M marker,
// so re-parsing the emitted text would rebind every slave to one master.
func splitMasterDBC(t *testing.T) DBCDefinition {
	t.Helper()
	return mirrorDBC(t,
		mirrorSignal("MuxA", 0, AlwaysPresent{}),
		mirrorSignal("MuxB", 8, AlwaysPresent{}),
		mirrorSignal("A", 16, Multiplexed{
			Multiplexor:     "MuxA",
			MultiplexValues: []MultiplexValue{0},
		}),
		mirrorSignal("B", 24, Multiplexed{
			Multiplexor:     "MuxB",
			MultiplexValues: []MultiplexValue{0},
		}),
	)
}

// hasWarning reports whether issues contains a warning-severity entry with
// the given code.
func hasWarning(issues []ValidationIssue, code IssueCode) bool {
	for _, issue := range issues {
		if issue.Code == code && issue.Severity == SeverityWarning {
			return true
		}
	}
	return false
}

// TestValidateDBC_MultiValueMuxSelectorWarning pins CHECK 24: validateDBC
// names the multi-value-selector shape with a warning and has_errors stays
// false.
func TestValidateDBC_MultiValueMuxSelectorWarning(t *testing.T) {
	client := newFFIClient(t)

	result, err := client.ValidateDBC(ctx, multiValueMuxDBC(t))
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if result.HasErrors {
		t.Errorf("has_errors = true, want false (warning-class only): %+v", result.Issues)
	}
	if !hasWarning(result.Issues, IssueMultiValueMuxSelector) {
		t.Errorf("expected a multi_value_mux_selector warning, got %+v", result.Issues)
	}
}

// TestValidateDBC_MuxMasterIncoherentWarning pins CHECK 25: validateDBC names
// the split-master shape with a warning and has_errors stays false.
func TestValidateDBC_MuxMasterIncoherentWarning(t *testing.T) {
	client := newFFIClient(t)

	result, err := client.ValidateDBC(ctx, splitMasterDBC(t))
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if result.HasErrors {
		t.Errorf("has_errors = true, want false (warning-class only): %+v", result.Issues)
	}
	if !hasWarning(result.Issues, IssueMuxMasterIncoherent) {
		t.Errorf("expected a mux_master_incoherent warning, got %+v", result.Issues)
	}
}

// TestValidateDBC_SingletonCoherentControls pins the negative direction: the
// singleton-selector, single-master control draws neither mirror warning.
func TestValidateDBC_SingletonCoherentControls(t *testing.T) {
	client := newFFIClient(t)

	control := mirrorDBC(t,
		mirrorSignal("Mux", 0, AlwaysPresent{}),
		mirrorSignal("A", 16, Multiplexed{
			Multiplexor:     "Mux",
			MultiplexValues: []MultiplexValue{0},
		}),
		mirrorSignal("B", 24, Multiplexed{
			Multiplexor:     "Mux",
			MultiplexValues: []MultiplexValue{1},
		}),
	)
	result, err := client.ValidateDBC(ctx, control)
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if hasWarning(result.Issues, IssueMultiValueMuxSelector) ||
		hasWarning(result.Issues, IssueMuxMasterIncoherent) {
		t.Errorf("control DBC drew a mirror warning: %+v", result.Issues)
	}
}

// TestParseDBC_MirrorWarningsDoNotBlockLoad pins the warning-class contract on
// the load route: both shapes load successfully, each surfacing its mirror
// warning on ParsedDBC.Warnings.
func TestParseDBC_MirrorWarningsDoNotBlockLoad(t *testing.T) {
	cases := []struct {
		name string
		dbc  DBCDefinition
		code IssueCode
	}{
		{"multi_value_mux_selector", multiValueMuxDBC(t), IssueMultiValueMuxSelector},
		{"mux_master_incoherent", splitMasterDBC(t), IssueMuxMasterIncoherent},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			client := newFFIClient(t)
			parsed, err := client.ParseDBC(ctx, tc.dbc)
			if err != nil {
				t.Fatalf("ParseDBC must load a warning-only shape: %v", err)
			}
			if !hasWarning(parsed.Warnings, tc.code) {
				t.Errorf("expected a %s warning on the load, got %+v", tc.code, parsed.Warnings)
			}
		})
	}
}
