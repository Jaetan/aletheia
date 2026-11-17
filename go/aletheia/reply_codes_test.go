// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"os"
	"path/filepath"
	"testing"
)

// IssueCodes and ErrorCodes are the sets the reply readers read a code from,
// for the parity test outside the package.
var (
	IssueCodes = issueCodes
	ErrorCodes = errorCodes
)

// issueReader reads a reply holding one validation issue, the issue's JSON
// text, answering nil where it reads the issue.
type issueReader func(t *testing.T, issue string) error

// liftedIssues answers nil for a refusal lifted to the typed error carrying
// its issues, and err for any other.
func liftedIssues(err error) error {
	var vfe *ValidationFailedError
	var trte *TextRoundTripFailedError
	if errors.As(err, &vfe) || errors.As(err, &trte) {
		return nil
	}
	return err
}

// issueReaders are the replies holding validation issues, by the key each
// holds them at: a validation, a loaded DBC's warnings, the two refusals that
// carry issues and a DBC text's diagnostics.
var issueReaders = map[string]struct {
	key  string
	read issueReader
}{
	"validation": {"issues", func(_ *testing.T, issue string) error {
		_, err := parseValidationResponse(`{"status":"validation","has_errors":false,"issues":[` + issue + `]}`)
		return err
	}},
	"loaded DBC": {"warnings", func(t *testing.T, issue string) error {
		t.Helper()
		dbc, err := os.ReadFile(filepath.Join(repoRoot(t), "python", "tests", "fixtures", "dbc_corpus", "parity_snapshots", "minimal.json"))
		if err != nil {
			t.Fatal(err)
		}
		_, err = parseParsedDBCResponse(`{"status":"success","dbc":` + string(dbc) + `,"warnings":[` + issue + `]}`)
		return err
	}},
	"validation refusal": {"issues", func(_ *testing.T, issue string) error {
		return liftedIssues(parseSuccessResponse(`{"status":"error","code":"handler_validation_failed","message":"m",` +
			`"has_errors":true,"issues":[` + issue + `]}`))
	}},
	"text round trip refusal": {"issues", func(_ *testing.T, issue string) error {
		return liftedIssues(parseSuccessResponse(`{"status":"error","code":"handler_text_roundtrip_failed","message":"m",` +
			`"has_errors":true,"issues":[` + issue + `]}`))
	}},
	"DBC text": {"issues", func(_ *testing.T, issue string) error {
		_, err := parseDBCTextResponse(`{"status":"success","text":"VERSION \"\"\n","issues":[` + issue + `]}`)
		return err
	}},
}

// requireIssueRefusals holds that every reader reads an issue of each of its
// two words or codes and refuses each arrival at <key>/<field> expecting
// expected, the arrival's text naming what came.
func requireIssueRefusals(t *testing.T, field, expected string, read []string, arrivals map[string]string) {
	t.Helper()
	for name, reader := range issueReaders {
		t.Run(name, func(t *testing.T) {
			for _, issue := range read {
				if err := reader.read(t, issue); err != nil {
					t.Errorf("%s: %v, want it read", issue, err)
				}
			}
			for issue, came := range arrivals {
				t.Run(came, func(t *testing.T) {
					requireReplyRefusal(t, reader.read(t, issue), "reply "+reader.key+"/"+field+": expected "+expected+", got "+came)
				})
			}
		})
	}
}

// A validation issue's severity is "error" or "warning", any other refused at
// its place, a word as well as nothing or a number.
func TestIssueSeverity_OutsideErrorAndWarningIsRefusedAtItsPlace(t *testing.T) {
	requireIssueRefusals(t, "severity", `"error" or "warning"`,
		[]string{
			`{"severity":"error","code":"factor_zero","detail":"d"}`,
			`{"severity":"warning","code":"factor_zero","detail":"d"}`,
		},
		map[string]string{
			`{"severity":"fatal","code":"factor_zero","detail":"d"}`: `"fatal"`,
			`{"code":"factor_zero","detail":"d"}`:                    "nothing",
			`{"severity":0,"code":"factor_zero","detail":"d"}`:       "number",
		})
}

// A validation issue's code is one of the IssueCodes, any other refused at its
// place, a word as well as nothing or a number.
func TestIssueCode_OutsideTheIssueCodesIsRefusedAtItsPlace(t *testing.T) {
	requireIssueRefusals(t, "code", "an issue code",
		[]string{
			`{"severity":"warning","code":"factor_zero","detail":"d"}`,
			`{"severity":"warning","code":"value_description_key_out_of_range","detail":"d"}`,
		},
		map[string]string{
			`{"severity":"warning","code":"some_future_code","detail":"d"}`: `"some_future_code"`,
			`{"severity":"warning","detail":"d"}`:                           "nothing",
			`{"severity":"warning","code":0,"detail":"d"}`:                  "number",
		})
}
