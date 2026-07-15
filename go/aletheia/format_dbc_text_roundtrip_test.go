// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"strings"
	"testing"
)

// TestFormatDBCText_SuccessCarriesTextAndIssues pins the decode of a
// formatDBCText success response into a *DBCText carrying the .dbc text image
// plus its wfTextIssues diagnostics (warning-severity, advisory).  The response
// is emitted only for a DBC that provably round-trips, so Issues is surfaced to
// the caller but may be empty; here a warning-severity issue exercises the shape.
func TestFormatDBCText_SuccessCarriesTextAndIssues(t *testing.T) {
	raw := `{"status":"success","text":"VERSION \"\"\n",` +
		`"issues":[{"severity":"warning","code":"unknown_value_description_target",` +
		`"detail":"VAL_ for an undeclared signal"}]}`
	out, err := parseDBCTextResponse(raw)
	if err != nil {
		t.Fatalf("parseDBCTextResponse: %v", err)
	}
	if out.Text != "VERSION \"\"\n" {
		t.Errorf("Text = %q, want the wire text image", out.Text)
	}
	if len(out.Issues) != 1 {
		t.Fatalf("len(Issues) = %d, want 1", len(out.Issues))
	}
	if out.Issues[0].Severity != SeverityWarning ||
		out.Issues[0].Code != IssueUnknownValueDescriptionTarget {
		t.Errorf("Issues[0] = %+v, want warning / unknown_value_description_target", out.Issues[0])
	}
}

// TestFormatDBCText_AbsentIssuesDefaultsEmpty confirms a success response with no
// issues field decodes to an empty Issues slice.
func TestFormatDBCText_AbsentIssuesDefaultsEmpty(t *testing.T) {
	out, err := parseDBCTextResponse(`{"status":"success","text":"x"}`)
	if err != nil {
		t.Fatalf("parseDBCTextResponse: %v", err)
	}
	if len(out.Issues) != 0 {
		t.Errorf("len(Issues) = %d, want 0 for an absent issues field", len(out.Issues))
	}
}

// TestFormatDBCText_NonArrayIssuesRejected confirms a present-but-non-array issues
// field is a protocol error, not silently dropped to empty (parity with
// Python/Rust; getArray alone would treat the wrong-type field as missing).
func TestFormatDBCText_NonArrayIssuesRejected(t *testing.T) {
	_, err := parseDBCTextResponse(`{"status":"success","text":"x","issues":{}}`)
	if err == nil {
		t.Fatal("expected a protocol error for a non-array issues field, got nil")
	}
	if !strings.Contains(err.Error(), "'issues' must be an array") {
		t.Errorf("Error() = %q, want it to mention 'issues' must be an array", err.Error())
	}
}

// TestFormatDBCText_RoundTripRefusalLifts pins the lift of a
// handler_text_roundtrip_failed envelope into a typed *TextRoundTripFailedError.
// FormatDBCText is always strict, so a DBC whose text does not round-trip (e.g. a
// multi-value mux) surfaces this typed refusal — led by the error-severity
// text_roundtrip_divergence issue, plus the multi_value_mux_selector diagnostic —
// rather than lossy text.  Error() stays byte-identical to the generic coded
// error the lift replaces.
func TestFormatDBCText_RoundTripRefusalLifts(t *testing.T) {
	const msg = "FormatDBCText: text round-trip failed: " +
		"re-parsing the emitted text does not reproduce the input DBC"
	raw := `{"status":"error","code":"handler_text_roundtrip_failed",` +
		`"message":"` + msg + `","has_errors":true,"issues":[` +
		`{"severity":"error","code":"text_roundtrip_divergence",` +
		`"detail":"re-parsing the emitted text does not reproduce the input DBC"},` +
		`{"severity":"warning","code":"multi_value_mux_selector",` +
		`"detail":"Message 'M': multi-value mux selector"}]}`
	out, err := parseDBCTextResponse(raw)
	if out != nil {
		t.Errorf("expected nil *DBCText on refusal, got %+v", out)
	}
	var trte *TextRoundTripFailedError
	if !errors.As(err, &trte) {
		t.Fatalf("expected *TextRoundTripFailedError, got %T: %v", err, err)
	}
	if !trte.HasErrors {
		t.Error("HasErrors = false, want true (decoded from the wire)")
	}
	if trte.Code != CodeHandlerTextRoundtripFailed {
		t.Errorf("Code = %q, want %q", trte.Code, CodeHandlerTextRoundtripFailed)
	}
	if len(trte.Issues) != 2 {
		t.Fatalf("len(Issues) = %d, want 2", len(trte.Issues))
	}
	if trte.Issues[0].Severity != SeverityError ||
		trte.Issues[0].Code != IssueTextRoundtripDivergence {
		t.Errorf("Issues[0] = %+v, want error / text_roundtrip_divergence", trte.Issues[0])
	}
	if trte.Issues[1].Code != IssueMultiValueMuxSelector {
		t.Errorf("Issues[1].Code = %q, want multi_value_mux_selector", trte.Issues[1].Code)
	}
	if want := "aletheia protocol error: " + msg; err.Error() != want {
		t.Errorf("Error() = %q, want byte-identical generic render %q", err.Error(), want)
	}
}
