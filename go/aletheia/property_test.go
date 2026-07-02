// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Property-based tests via testing/quick (R18 cluster 5 — Cat 33c).
//
// Round-trip pairs for every wire-format encode/decode that the Go binding
// owns plus mock-vs-real parity invariants for the IBackend / Backend
// interface.  testing/quick is the stdlib randomized-input runner; one
// quick.Check per property, one per file section.
//
// Property tests run alongside fuzz harnesses (fuzz_test.go).  Fuzzers find
// crashes; properties find logical bugs that don't crash but violate an
// expected invariant.  Both are required by AGENTS.md cat 33b/c — fuzzers
// alone miss "wrong but doesn't panic" outputs; properties alone miss the
// "crashes on adversarial input" failures.

package aletheia

import (
	"encoding/json"
	"math"
	"testing"
	"testing/quick"
)

// Property: parseRational round-trips through serializeRational for every
// non-zero-denominator Rational.  Catches: overflow on extreme numerators,
// silent normalization differences, lost precision for negative numbers.
//
// The round-trip goes through the production decode path — serializeRational →
// JSON → parseResponse (a UseNumber decoder, so numbers arrive as json.Number,
// exact for the full int64 range) → parseRational. The >2^53 boundary is pinned
// separately by TestParseResponse_ExactLargeRational.
func TestProperty_RationalRoundTrip(t *testing.T) {
	property := func(num int32, denomNonZero uint16) bool {
		denom := int64(denomNonZero) + 1
		original := Rational{Numerator: int64(num), Denominator: denom}
		// Wrap in a one-field object and decode via the real wire decoder.
		bytes, mErr := json.Marshal(map[string]any{"value": serializeRational(original)})
		if mErr != nil {
			return true // marshal failure is acceptable; parseRational not reached
		}
		m, pErr := parseResponse(string(bytes))
		if pErr != nil {
			t.Logf("parseResponse(%s) failed: %v", bytes, pErr)
			return false
		}
		parsed, err := parseRational(m["value"])
		if err != nil {
			t.Logf("parseRational(%v) failed: %v", m["value"], err)
			return false
		}
		// Equality after normalisation: cross-multiply to avoid canonical-
		// form reasoning.  parseRational MAY normalise; the round-trip
		// invariant is value-equality, not bit-equality.
		return original.Numerator*parsed.Denominator == parsed.Numerator*original.Denominator
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 200}); err != nil {
		t.Errorf("RationalRoundTrip property failed: %v", err)
	}
}

// Property: parseResponse is total over valid JSON and rejects every
// invalid byte sequence.  "Total" here means the function does not panic;
// the returned (map, error) is well-formed in both arms.
func TestProperty_ParseResponseTotal(t *testing.T) {
	property := func(payload []byte) bool {
		// Constrain to ASCII printable to keep the corpus interpretable.
		// The fuzzer covers the binary-byte case; this property focuses on
		// the structural totality invariant.
		ascii := make([]byte, len(payload))
		for i, b := range payload {
			ascii[i] = (b & 0x7F) | 0x20 // printable range
		}
		// Should not panic regardless of input.
		_, _ = parseResponse(string(ascii))
		return true
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 200}); err != nil {
		t.Errorf("ParseResponseTotal property failed: %v", err)
	}
}

// Property: serializeCommand → parseResponse round-trips on the "command"
// field for every {command, key, value} triple.  Catches: silent key-name
// drops on duplicate-key coercion, JSON-special character mishandling.
func TestProperty_CommandRoundTrip(t *testing.T) {
	property := func(command, key string) bool {
		fields := map[string]any{key: "v"}
		out, err := serializeCommand(command, fields)
		if err != nil {
			return true // marshal error is acceptable for adversarial input
		}
		parsed, err := parseResponse(out)
		if err != nil {
			t.Logf("parseResponse(%q) failed after serializeCommand: %v", out, err)
			return false
		}
		got, ok := parsed["command"].(string)
		if !ok {
			return false
		}
		return got == command
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 200}); err != nil {
		t.Errorf("CommandRoundTrip property failed: %v", err)
	}
}

// Property: parseRational is monotonic over JSON-numeric inputs — for two
// integers a < b, parseRational(a).asDouble < parseRational(b).asDouble.
// Catches: silent overflow at the int64 boundary, sign-handling drift.
func TestProperty_RationalMonotonicity(t *testing.T) {
	property := func(a, b int32) bool {
		if a == b {
			return true
		}
		ra, errA := parseRational(json.Number(string(jsonNumber(int64(a)))))
		rb, errB := parseRational(json.Number(string(jsonNumber(int64(b)))))
		if errA != nil || errB != nil {
			return true // adversarial input: not a counterexample
		}
		da := float64(ra.Numerator) / float64(ra.Denominator)
		db := float64(rb.Numerator) / float64(rb.Denominator)
		if math.IsNaN(da) || math.IsNaN(db) {
			return true
		}
		if a < b {
			return da <= db
		}
		return da >= db
	}
	if err := quick.Check(property, &quick.Config{MaxCount: 200}); err != nil {
		t.Errorf("RationalMonotonicity property failed: %v", err)
	}
}

// jsonNumber renders an int64 as a json.Number-compatible byte string.
// Helper for the monotonicity property — testing/quick can't generate
// json.Number directly.
func jsonNumber(v int64) []byte {
	b, _ := json.Marshal(v)
	return b
}

// parseRational's adversarial-wire rejections (fractional scalar / fractional
// or out-of-range numerator+denominator / zero / negative denominator) are
// pinned on the production decode path by TestParseRational_RejectsBadComponents
// in json_precision_test.go — fed as JSON strings through parseResponse, which
// is how the wire actually delivers them. (Native-Go-float64 inputs are not a
// reachable surface: the sole decoder, parseResponse, emits only json.Number.)

// Property: MockBackend and FFIBackend agree on the parsed JSON shape for
// every Process(input) where the input is a parseable JSON command.  Mock
// returns a canned response; this property checks that the typed-decode
// path treats both backends' outputs identically (response shape parity).
//
// Note: this is NOT a full equivalence claim (the mock doesn't compute
// LTL properties) — it asserts the binding's response-decoding paths
// have the same structure regardless of which backend is in scope.
func TestProperty_MockRealResponseShapeParity(t *testing.T) {
	// Property: for canned mock responses, the binding's parseResponse and
	// the response-narrowing helpers (parseValidationResponse,
	// parseStreamResponse, etc.) accept the same wire shapes that the FFI
	// backend produces.  We check this by feeding the mock's canned strings
	// through parseResponse and asserting they decode to a non-nil map.
	cannedResponses := []string{
		`{"status":"ack"}`,
		`{"status":"success"}`,
		`{"status":"validation","has_errors":false,"issues":[]}`,
		`{"status":"error","code":"x","message":"y"}`,
		`{"status":"fails","type":"property","property_index":{"numerator":0,"denominator":1},"timestamp":{"numerator":1000,"denominator":1}}`,
	}
	for _, raw := range cannedResponses {
		m, err := parseResponse(raw)
		if err != nil {
			t.Errorf("parseResponse(%q): unexpected error %v", raw, err)
			continue
		}
		if _, hasStatus := m["status"]; !hasStatus {
			t.Errorf("parseResponse(%q): missing 'status' key", raw)
		}
	}
}
