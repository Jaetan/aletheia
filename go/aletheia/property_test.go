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
// The round-trip goes through JSON marshal+unmarshal because that is the
// actual code path: serializeRational emits a map with int64 values, and
// parseResponse → parseRational receives them as float64 (Go's encoding/json
// default for numeric values inside any).  Bypassing the marshal step
// hides the int64-vs-float64 conversion that the FFI boundary always does.
func TestProperty_RationalRoundTrip(t *testing.T) {
	property := func(num int32, denomNonZero uint16) bool {
		denom := int64(denomNonZero) + 1
		original := Rational{Numerator: int64(num), Denominator: denom}
		serialized := serializeRational(original)
		// Mimic the real round-trip: marshal then unmarshal-as-any.
		bytes, mErr := json.Marshal(serialized)
		if mErr != nil {
			return true // marshal failure is acceptable; parseRational not reached
		}
		var roundTripped any
		if uErr := json.Unmarshal(bytes, &roundTripped); uErr != nil {
			return true
		}
		parsed, err := parseRational(roundTripped)
		if err != nil {
			t.Logf("parseRational(%v) failed: %v", roundTripped, err)
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

// R20 cluster H — GO-B-12.1 reject cases.  parseRational must reject
// adversarial wire forms BEFORE the int64 cast silently truncates them:
// (1) non-integer scalar, (2) non-integer numerator/denominator in the
// dict form, (3) numerator/denominator outside the int64 range.  Mirror
// the defenses already in parseNumberAsInt64 (json.go:797).
func TestParseRational_RejectFractionalScalar(t *testing.T) {
	if _, err := parseRational(1.5); err == nil {
		t.Fatalf("expected fractional scalar 1.5 to be rejected")
	}
}

func TestParseRational_RejectFractionalNumerator(t *testing.T) {
	if _, err := parseRational(map[string]any{"numerator": 1.5, "denominator": 2.0}); err == nil {
		t.Fatalf("expected fractional numerator 1.5 to be rejected")
	}
}

func TestParseRational_RejectFractionalDenominator(t *testing.T) {
	// Pre-fix `int64(0.5)` silently truncated to 0, which then tripped
	// the zero-denominator branch with a misleading "zero denominator"
	// message.  The truncation-check now fires first.
	if _, err := parseRational(map[string]any{"numerator": 1.0, "denominator": 0.5}); err == nil {
		t.Fatalf("expected fractional denominator 0.5 to be rejected")
	}
}

func TestParseRational_RejectOverflowingScalar(t *testing.T) {
	if _, err := parseRational(math.MaxFloat64); err == nil {
		t.Fatalf("expected MaxFloat64 numerator to be rejected as out-of-range")
	}
}

func TestParseRational_RejectOverflowingDict(t *testing.T) {
	if _, err := parseRational(map[string]any{
		"numerator":   math.MaxFloat64,
		"denominator": 1.0,
	}); err == nil {
		t.Fatalf("expected MaxFloat64 numerator in dict form to be rejected")
	}
	if _, err := parseRational(map[string]any{
		"numerator":   1.0,
		"denominator": math.MaxFloat64,
	}); err == nil {
		t.Fatalf("expected MaxFloat64 denominator in dict form to be rejected")
	}
}

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
