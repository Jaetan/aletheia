//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import "testing"

// htmlCommentDBCText is a one-message DBC text whose comment holds the three
// characters encoding/json writes as <, > and &.
const htmlCommentDBCText = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: N\n\nBO_ 1 M: 8 N\n" +
	" SG_ S : 0|8@1+ (1,0) [0|1] \"u\" N\n\nCM_ \"a<b&c>d\";\n"

// The kernel reads a \u escape as the character it names, so a DBC text
// holding '<', '>' or '&' loads through the Go client, whose encoder writes
// each of them escaped.
func TestDBCTextWithHTMLCharactersLoads(t *testing.T) {
	parsed, err := newFFIClient(t).ParseDBCText(t.Context(), htmlCommentDBCText)
	if err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	if len(parsed.DBC.Comments) != 1 || parsed.DBC.Comments[0].Text != "a<b&c>d" {
		t.Errorf("the comment came back as %+v", parsed.DBC.Comments)
	}
}
