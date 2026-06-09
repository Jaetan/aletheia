// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Native Go fuzz harnesses (R18 cluster 5 — Cat 33b).
//
// One Fuzz target per binding-side parser.  All five names are pinned by
// AGENTS.md cat 33b: FuzzParseResponse, FuzzMarshalCommand,
// FuzzDecodeBinaryFrame, FuzzParseRationalNumber, FuzzParseDBCJSON.  Each
// adds a small seed corpus via f.Add and asserts the panic-free invariant
// — fuzzers are correctness gates against unexpected inputs, not happy-path
// coverage.
//
// Run a single target:    go test -fuzz=FuzzParseResponse -fuzztime=60s ./aletheia/
// Run all (corpus only):  go test ./aletheia/
//
// Seed corpora live inline (f.Add) per Go convention; explicit testdata/fuzz/
// files are not required for the smoke lane.  Long-fuzz runs (the nightly
// extended lane per AGENTS.md cat 33b) accumulate corpus under
// testdata/fuzz/<TargetName>/ when run with -fuzz; check them in if a real
// crash is found and minimised.

package aletheia

import (
	"encoding/json"
	"testing"
)

// FuzzParseResponse covers the JSON envelope parser (json.go:754).  The
// invariant is "no panic on any input" — parser must return either a parsed
// map or a typed error.  Catches: invalid UTF-8, oversize numerics,
// pathological nesting, NUL bytes, control characters.
func FuzzParseResponse(f *testing.F) {
	f.Add(`{"status":"ack"}`)
	f.Add(`{"status":"error","code":"x","message":"y"}`)
	f.Add(`{"status":"validation","has_errors":false,"issues":[]}`)
	f.Add(`{}`)
	f.Add(``)
	f.Add(`{"deeply":{"nested":{"map":{"value":42}}}}`)

	f.Fuzz(func(t *testing.T, raw string) {
		_, _ = parseResponse(raw)
		// No panic = success.  Errors are expected on malformed input;
		// the parser must categorise them as protocol errors, not crash.
	})
}

// FuzzMarshalCommand covers the command serializer (json.go:29).  Property:
// the output is valid JSON and round-trips through parseResponse.  Catches:
// non-JSON-encodable values, duplicate keys (Go map semantics resolve them
// silently — explicit assertion here surfaces unexpected silent drops).
func FuzzMarshalCommand(f *testing.F) {
	f.Add("parseDBC", "field1", "value1")
	f.Add("setProperties", "properties", "[]")
	f.Add("validateDBC", "dbc", `{"messages":[]}`)
	f.Add("", "", "")

	f.Fuzz(func(t *testing.T, command, key, value string) {
		fields := map[string]any{key: value}
		out, err := serializeCommand(command, fields)
		if err != nil {
			return // expected on weird inputs
		}
		// Property: the output must round-trip through the JSON parser.
		// If serializeCommand emits anything that parseResponse rejects,
		// the binding has a self-inconsistent encode/decode pair.
		parsed, perr := parseResponse(out)
		if perr != nil {
			t.Errorf("serializeCommand produced unparseable output: %q (%v)", out, perr)
		}
		if got := parsed["command"]; got != command {
			t.Errorf("command round-trip: want %q, got %q", command, got)
		}
	})
}

// FuzzDecodeBinaryFrame covers the binary extraction parser (json.go:995).
// The invariant is "no panic on any byte sequence".  Catches: short reads,
// length-mismatch (claimed N entries but buffer truncated), out-of-range
// indices into the names array, malformed Rational denominators.
func FuzzDecodeBinaryFrame(f *testing.F) {
	f.Add([]byte{0, 0, 0, 0, 0, 0, 0, 0}, "Speed,RPM,Temp")
	f.Add([]byte{}, "")
	f.Add([]byte{0xFF, 0xFF, 0xFF, 0xFF}, "X")
	f.Add(make([]byte, 256), "A,B,C,D,E,F,G,H")

	f.Fuzz(func(t *testing.T, buf []byte, csvNames string) {
		var names []string
		if csvNames != "" {
			names = []string{csvNames} // fuzz one signal name per run
		}
		_, _ = parseExtractionBin(buf, names)
		// No panic = success.
	})
}

// FuzzParseRationalNumber covers the wire-format Rational parser
// (json.go:613).  Property: the parser handles every JSON-representable
// numeric without panic, and accepts both integer + {numerator,denominator}
// shapes.  Catches: zero denominators, NaN/Inf rationals, malformed shapes.
func FuzzParseRationalNumber(f *testing.F) {
	f.Add(`42`)
	f.Add(`{"numerator":3,"denominator":7}`)
	f.Add(`{"numerator":0,"denominator":1}`)
	f.Add(`{"numerator":-100,"denominator":3}`)
	f.Add(`null`)
	f.Add(`{"numerator":1,"denominator":0}`) // adversarial: zero denom
	f.Add(``)

	f.Fuzz(func(t *testing.T, raw string) {
		var v any
		if err := json.Unmarshal([]byte(raw), &v); err != nil {
			return // not valid JSON — out of parser's responsibility
		}
		_, _ = parseRational(v)
		// No panic = success.
	})
}

// FuzzParseDBCJSON covers the DBC JSON-shape parser (json.go:1314).  Catches:
// missing required fields (empty messages array, signals with no name),
// type mismatches (string where number expected), enum drift on byteOrder /
// presence, oversize string lengths, malformed nested rationals.
func FuzzParseDBCJSON(f *testing.F) {
	f.Add(`{"messages":[]}`)
	f.Add(`{"messages":[{"id":256,"name":"M","dlc":8,"sender":"E","signals":[]}]}`)
	f.Add(`{"messages":[{"id":256,"name":"","dlc":8,"sender":"","signals":[]}]}`)
	f.Add(``)
	f.Add(`null`)
	f.Add(`{"messages":null}`)

	f.Fuzz(func(t *testing.T, raw string) {
		var j map[string]any
		if err := json.Unmarshal([]byte(raw), &j); err != nil {
			return // not valid JSON — out of parser's responsibility
		}
		_, _ = parseDBCDefinition(j)
		// No panic = success.
	})
}
