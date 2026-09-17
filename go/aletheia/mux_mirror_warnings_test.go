//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Two mux shapes stream perfectly well and cannot be written back as .dbc
// text: a signal multiplexed on more than one selector value, and slaves split
// under two masters. The validator names both with a warning rather than an
// error, under multi_value_mux_selector and mux_master_incoherent, which the
// protocol document lists among the codes validateDBC and the loading routes
// share with the text formatter.
//
// These run against the library, not a mock: the decision is the kernel's, and
// a mock would only show that a wire shape came back. Both shapes are built
// here as values, the text parser being unable to express either.

package aletheia

import "testing"

// mirrorSignal is an eight-bit unsigned signal at unit scale, the shape the
// Python validator tests use for the same checks.
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

// multiValueMuxDBC multiplexes one signal on two selector values. The text
// form carries only the first, so writing it out loses the second.
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

// splitMasterDBC puts its slaves under two masters. Both masters exist, so no
// error-class check fires, but the text form marks one master per message, and
// reading it back would bind every slave to that one.
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

// hasWarning reports whether the code is among the issues, at warning
// severity: the severity is part of the claim, an error-class entry of the
// same code being a different outcome.
func hasWarning(issues []ValidationIssue, code IssueCode) bool {
	for _, issue := range issues {
		if issue.Code == code && issue.Severity == SeverityWarning {
			return true
		}
	}
	return false
}

// Each shape is named with its warning, and nothing is named on the shape
// that is coherent. The errors flag stays down throughout: these shapes load.
func TestValidateDBC_NamesTheMirrorShapes(t *testing.T) {
	coherent := func(t *testing.T) DBCDefinition {
		t.Helper()
		return mirrorDBC(t,
			mirrorSignal("Mux", 0, AlwaysPresent{}),
			mirrorSignal("A", 16, Multiplexed{Multiplexor: "Mux", MultiplexValues: []MultiplexValue{0}}),
			mirrorSignal("B", 24, Multiplexed{Multiplexor: "Mux", MultiplexValues: []MultiplexValue{1}}),
		)
	}
	cases := map[string]struct {
		dbc  func(*testing.T) DBCDefinition
		want IssueCode
	}{
		"a selector with two values":  {multiValueMuxDBC, IssueMultiValueMuxSelector},
		"slaves under two masters":    {splitMasterDBC, IssueMuxMasterIncoherent},
		"one selector and one master": {coherent, ""},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			client := newFFIClient(t)
			result, err := client.ValidateDBC(ctx, tc.dbc(t))
			if err != nil {
				t.Fatalf("ValidateDBC: %v", err)
			}
			if result.HasErrors {
				t.Errorf("the shape was refused as an error rather than named as a warning: %+v", result.Issues)
			}
			for _, code := range []IssueCode{IssueMultiValueMuxSelector, IssueMuxMasterIncoherent} {
				got := hasWarning(result.Issues, code)
				if want := code == tc.want; got != want {
					t.Errorf("warning %s present = %v, want %v: %+v", code, got, want, result.Issues)
				}
			}
		})
	}
}

// The loading route says the same thing: both shapes load, each carrying its
// warning, so a caller sees the shape named without being refused.
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
