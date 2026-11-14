// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import "testing"

// A string that came where a word was expected is quoted as Python's reply
// refusals quote it, json.dumps with every character past ASCII escaped: the
// quote, the backslash and the five control characters JSON names by their
// escape, every other control character, DEL and every character up to
// U+FFFF as \u and four lowercase hex digits, a character above U+FFFF as its
// surrogate pair, and printable ASCII as itself up to each of its edges.
func TestQuoteJSON_QuotesEveryClassAsPythonDoes(t *testing.T) {
	cases := map[string]string{
		`"`:          `"\""`,
		`\`:          `"\\"`,
		"\b":         `"\b"`,
		"\f":         `"\f"`,
		"\n":         `"\n"`,
		"\r":         `"\r"`,
		"\t":         `"\t"`,
		"\x00":       `"\u0000"`,
		"\x1f":       `"\u001f"`,
		" ":          `" "`,
		"~":          `"~"`,
		"\x7f":       `"\u007f"`,
		"\u0080":     `"\u0080"`,
		"\uffff":     `"\uffff"`,
		"\U00010000": `"\ud800\udc00"`,
		"\U0010ffff": `"\udbff\udfff"`,
		"word":       `"word"`,
	}
	for s, want := range cases {
		if got := quoteJSON(s); got != want {
			t.Errorf("quoteJSON(%+q) = %s, want %s", s, got, want)
		}
	}
}
