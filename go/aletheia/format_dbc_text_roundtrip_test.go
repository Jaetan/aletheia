// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"testing"
)

// The decoder of a formatDBCText response, over crafted wire text. The command
// is always strict: the kernel answers text only for a DBC it has proved
// re-parses, and refuses the rest with a typed error, so the two shapes below
// are the whole surface.

// A success carries the text image and whatever advisory issues came with it.
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

// The kernel writes the issues whatever they are, so a success without the
// field is refused there, and an empty one carries no issues rather than a
// nil the caller has to test for.
func TestFormatDBCText_IssuesAreRead(t *testing.T) {
	_, err := parseDBCTextResponse(`{"status":"success","text":"x"}`)
	if want := "reply issues: expected array, got nothing"; err == nil || err.Error() != want {
		t.Errorf("got %v, want %q", err, want)
	}
	out, err := parseDBCTextResponse(`{"status":"success","text":"x","issues":[]}`)
	if err != nil {
		t.Fatalf("parseDBCTextResponse: %v", err)
	}
	if out.Issues == nil || len(out.Issues) != 0 {
		t.Errorf("Issues = %#v, want empty and not nil", out.Issues)
	}
}

// Every response the decoder cannot trust is refused with a protocol error
// naming the place and what came there: a status that is neither success nor
// an error envelope, a text field missing or of the wrong type, and an issues
// field that is not an array of objects each carrying a severity. The Python and Rust decoders refuse the wrong-typed issues
// field too, where reading it through a helper that treats a wrong type as
// absent would have dropped it.
func TestFormatDBCText_RefusesMalformedResponses(t *testing.T) {
	cases := map[string]struct {
		raw  string
		want string
	}{
		"status is neither":    {`{"status":"pending","text":"x"}`, `reply status: expected "success" or "error", got "pending"`},
		"no text":              {`{"status":"success"}`, "reply text: expected string, got nothing"},
		"text is not a string": {`{"status":"success","text":3}`, "reply text: expected string, got number"},
		"issues is not a list": {`{"status":"success","text":"x","issues":{}}`, "reply issues: expected array, got object"},
		"an issue is not an object": {
			`{"status":"success","text":"x","issues":["divergence"]}`, "reply issues: expected object, got string"},
		"an issue has no severity": {
			`{"status":"success","text":"x","issues":[{"code":"text_roundtrip_divergence","detail":"d"}]}`,
			`reply issues/severity: expected "error" or "warning", got nothing`},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			out, err := parseDBCTextResponse(tc.raw)
			if out != nil {
				t.Errorf("expected no text on a refusal, got %+v", out)
			}
			if err == nil {
				t.Fatal("expected a protocol error, got nil")
			}
			if err.Error() != tc.want {
				t.Errorf("Error() = %q, want %q", err.Error(), tc.want)
			}
		})
	}
}

// A DBC whose text does not re-parse, a multi-value mux selector among the
// reasons, is refused as a typed error carrying the issues that led to it.
// The rendered message stays what the generic coded error would have printed,
// so lifting the type changes what a caller can match on and not what it
// reads.
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
		t.Error("HasErrors = false, want true from the wire")
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
	if want := msg; err.Error() != want {
		t.Errorf("Error() = %q, want the generic render %q", err.Error(), want)
	}
}
