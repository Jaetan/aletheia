//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// VAL_ value descriptions land on DBCSignal.ValueDescriptions, come back
// out through the text formatter, and a VAL_ line aimed at a message and
// signal the text never declares raises the validator's
// UnknownValueDescriptionTarget warning. The promotion runs through the
// kernel's parser, formatter and validator, so these tests use the real
// library rather than a mock, which could only see the wire shape.

package aletheia

import (
	"reflect"
	"strings"
	"testing"
)

// newFFIClient is a client over the built library, closed when the test
// ends; the test is skipped when the library is not built.
func newFFIClient(t *testing.T) *Client {
	t.Helper()
	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
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
		if err := closeWithin(t, client); err != nil {
			t.Errorf("Close: %v", err)
		}
	})
	return client
}

// valDBCText is a one-message DBC text whose VAL_ line is the argument.
func valDBCText(message, valLine string) string {
	return "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n" + message + "\n\n" + valLine + "\n"
}

// A VAL_ line's entries land on the signal in order, and the formatter writes
// the line back.
func TestParseDBCText_ValueDescriptionsRoundTrip(t *testing.T) {
	ctx := bounded(t)
	client := newFFIClient(t)
	const valLine = `VAL_ 300 EngineState 0 "Off" 1 "Cranking" 2 "Running" 3 "Stall" ;`
	text := valDBCText("BO_ 300 Transmission: 8 ECU\n SG_ EngineState : 8|2@1+ (1,0) [0|3] \"\" Vector__XXX", valLine)

	parsed, err := client.ParseDBCText(ctx, text)
	if err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	if len(parsed.DBC.Messages) != 1 || len(parsed.DBC.Messages[0].Signals) != 1 {
		t.Fatalf("unexpected DBC shape: %+v", parsed.DBC)
	}
	want := []DBCValueEntry{{0, "Off"}, {1, "Cranking"}, {2, "Running"}, {3, "Stall"}}
	if got := parsed.DBC.Messages[0].Signals[0].ValueDescriptions; !reflect.DeepEqual(got, want) {
		t.Errorf("value descriptions: got %+v, want %+v", got, want)
	}

	out, err := client.FormatDBCText(ctx, parsed.DBC)
	if err != nil {
		t.Fatalf("FormatDBCText: %v", err)
	}
	if !strings.Contains(out.Text, valLine) {
		t.Errorf("expected the VAL_ line in the formatted output, got:\n%s", out.Text)
	}
}

// A VAL_ line naming a message and signal the text does not declare loads
// with the UnknownValueDescriptionTarget warning among the parse warnings.
func TestParseDBCText_UnknownValueDescriptionTargetWarning(t *testing.T) {
	ctx := bounded(t)
	client := newFFIClient(t)
	text := valDBCText("BO_ 256 Engine: 8 ECU\n SG_ Rpm : 0|16@1+ (1,0) [0|8000] \"rpm\" Vector__XXX", `VAL_ 999 GhostSignal 0 "Off" 1 "On" ;`)

	parsed, err := client.ParseDBCText(ctx, text)
	if err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	for _, w := range parsed.Warnings {
		if w.Code == IssueUnknownValueDescriptionTarget {
			return
		}
	}
	t.Errorf("expected an unknown_value_description_target warning, got %+v", parsed.Warnings)
}
