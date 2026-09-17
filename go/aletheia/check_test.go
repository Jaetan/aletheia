// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"errors"
	"math"
	"strings"
	"testing"
)

// mustDesc renders a check's condition description, failing the test on a
// renderer error. The thresholds go through the kernel renderer, so the GHC
// runtime must be up; TestMain in main_test.go brings it up for the package.
func mustDesc(t *testing.T, r CheckResult) string {
	t.Helper()
	s, err := r.ConditionDesc()
	if err != nil {
		t.Fatalf("ConditionDesc: %v", err)
	}
	return s
}

func half(n int64) Rational { return Rational{Numerator: n, Denominator: 2} }

// built wraps an infallible builder result as the fallible shape the tables use.
func built(r CheckResult) func() (CheckResult, error) {
	return func() (CheckResult, error) { return r, nil }
}

// Every builder produces the formula its name promises, read through the
// formula printer; where a manual construction of the same formula exists,
// it prints the same, so the builder is a shorthand and not a variant.
func TestCheckFormulas(t *testing.T) {
	cases := []struct {
		name   string
		build  func() (CheckResult, error)
		want   string
		manual Formula
	}{
		{
			"never exceeds",
			built(CheckSignal("Speed").NeverExceeds(IntRational(220))),
			"always(Speed <= 220)",
			Always{Inner: Atomic{Predicate: LessThanOrEqual{Signal: "Speed", Value: IntRational(220)}}},
		},
		{
			"never below",
			built(CheckSignal("Voltage").NeverBelow(half(23))),
			"always(Voltage >= 11.5)",
			nil,
		},
		{
			"stays between",
			func() (CheckResult, error) { return CheckSignal("Voltage").StaysBetween(half(23), half(29)) },
			"always(11.5 <= Voltage <= 14.5)",
			Always{Inner: Atomic{Predicate: Between{Signal: "Voltage", Min: half(23), Max: half(29)}}},
		},
		{
			"never equals",
			built(CheckSignal("ErrorCode").NeverEquals(IntRational(255))),
			"never ErrorCode = 255",
			Never(Equals{Signal: "ErrorCode", Value: IntRational(255)}),
		},
		{
			"equals always",
			built(CheckSignal("Gear").Equals(IntRational(0)).Always()),
			"always(Gear = 0)",
			nil,
		},
		{
			"settles between within",
			func() (CheckResult, error) {
				return CheckSignal("Temp").SettlesBetween(IntRational(60), IntRational(80)).Within(500)
			},
			"always within 500ms (60 <= Temp <= 80)",
			AlwaysWithin(TimeBound{Microseconds: 500_000},
				Atomic{Predicate: Between{Signal: "Temp", Min: IntRational(60), Max: IntRational(80)}}),
		},
		{
			"when exceeds then equals within",
			func() (CheckResult, error) {
				return CheckWhen("Brake").Exceeds(IntRational(50)).Then("BrakeLight").Equals(IntRational(1)).Within(100)
			},
			"always(not(Brake > 50) or eventually within 100ms (BrakeLight = 1))",
			nil,
		},
		{
			"when drops below then equals within",
			func() (CheckResult, error) {
				return CheckWhen("Voltage").DropsBelow(IntRational(11)).Then("Warning").Equals(IntRational(1)).Within(50)
			},
			"always(not(Voltage < 11) or eventually within 50ms (Warning = 1))",
			nil,
		},
		{
			"when equals then exceeds within",
			func() (CheckResult, error) {
				return CheckWhen("Ignition").Equals(IntRational(1)).Then("FuelPump").Exceeds(IntRational(0)).Within(50)
			},
			"always(not(Ignition = 1) or eventually within 50ms (FuelPump > 0))",
			nil,
		},
		{
			"when exceeds then stays between within",
			func() (CheckResult, error) {
				return CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed").StaysBetween(IntRational(0), IntRational(10)).Within(200)
			},
			"always(not(Brake > 50) or eventually within 200ms (0 <= Speed <= 10))",
			nil,
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			r, err := tc.build()
			if err != nil {
				t.Fatalf("build: %v", err)
			}
			if got := FormatFormula(r.Formula()); got != tc.want {
				t.Errorf("formula: got %q, want %q", got, tc.want)
			}
			if tc.manual != nil {
				if got := FormatFormula(tc.manual); got != tc.want {
					t.Errorf("manual construction prints %q, want %q", got, tc.want)
				}
			}
		})
	}
}

// An inverted range is refused where it is given, or surfaced by Within when
// the chain defers it, and the message names the two bounds.
func TestCheckInvertedRanges(t *testing.T) {
	cases := map[string]func() error{
		"stays between": func() error {
			_, err := CheckSignal("Voltage").StaysBetween(half(29), half(23))
			return err
		},
		"settles between within": func() error {
			_, err := CheckSignal("Temp").SettlesBetween(IntRational(80), IntRational(60)).Within(500)
			return err
		},
		"when then stays between within": func() error {
			_, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed").StaysBetween(IntRational(10), IntRational(0)).Within(200)
			return err
		},
	}
	for name, build := range cases {
		err := build()
		if err == nil {
			t.Errorf("%s: an inverted range was accepted", name)
			continue
		}
		if !strings.Contains(err.Error(), "must be <= hi") {
			t.Errorf("%s: the message does not name the bounds: %v", name, err)
		}
	}
}

// The millisecond bound is refused when negative and when its microsecond
// conversion would overflow int64; the largest representable bound is
// accepted. Both Within chains behave the same.
func TestCheckWithinBounds(t *testing.T) {
	const largest = math.MaxInt64 / usPerMillisecond
	chains := map[string]func(int64) error{
		"settles": func(ms int64) error {
			_, err := CheckSignal("T").SettlesBetween(IntRational(0), IntRational(1)).Within(ms)
			return err
		},
		"causal": func(ms int64) error {
			_, err := CheckWhen("A").Exceeds(IntRational(0)).Then("B").Equals(IntRational(1)).Within(ms)
			return err
		},
	}
	for name, within := range chains {
		if err := within(-1); err == nil || !strings.Contains(err.Error(), "non-negative") {
			t.Errorf("%s: expected a refusal of a negative bound, got %v", name, err)
		}
		if err := within(largest); err != nil {
			t.Errorf("%s: the largest bound was refused: %v", name, err)
		}
		if err := within(largest + 1); err == nil || !strings.Contains(err.Error(), "overflows") {
			t.Errorf("%s: expected an overflow refusal one past the largest bound, got %v", name, err)
		}
	}
}

// The range check cross-multiplies without overflow: these operands make the
// naive int64 products wrap, and the order still comes out right both ways.
func TestCheckStaysBetweenLargeOperands(t *testing.T) {
	lo := Rational{Numerator: math.MaxInt64, Denominator: 2}
	hi := Rational{Numerator: math.MaxInt64/2 + 1, Denominator: 1}
	if _, err := CheckSignal("S").StaysBetween(lo, hi); err != nil {
		t.Errorf("lo <= hi with large operands was refused: %v", err)
	}
	if _, err := CheckSignal("S").StaysBetween(hi, lo); err == nil {
		t.Error("an inverted range with large operands was accepted")
	}
}

// Each check names its primary signal and describes its condition with the
// thresholds rendered by the kernel: 1000000 stays 1000000, where Go's %g
// would print 1e+06, which is what pins the delegation.
func TestCheckSignalNameAndConditionDesc(t *testing.T) {
	causal, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("Light").Equals(IntRational(1)).Within(100)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	cases := []struct {
		check  CheckResult
		signal SignalName
		desc   string
	}{
		{CheckSignal("Speed").NeverExceeds(IntRational(220)), "Speed", "<= 220"},
		{CheckSignal("V").NeverBelow(half(23)), "V", ">= 11.5"},
		{CheckSignal("E").NeverEquals(IntRational(0)), "E", "!= 0"},
		{CheckSignal("X").NeverExceeds(IntRational(1000000)), "X", "<= 1000000"},
		{causal, "Light", "= 1 within 100ms"},
	}
	for _, tc := range cases {
		if got := tc.check.SignalName(); got != tc.signal {
			t.Errorf("SignalName: got %q, want %q", got, tc.signal)
		}
		if got := mustDesc(t, tc.check); got != tc.desc {
			t.Errorf("ConditionDesc: got %q, want %q", got, tc.desc)
		}
	}
}

func TestCheckMetadataNamedSeverity(t *testing.T) {
	r := CheckSignal("Speed").NeverExceeds(IntRational(220)).Named("SpeedLimit").Severity("critical")
	if r.Name() != "SpeedLimit" {
		t.Errorf("Name: got %q, want %q", r.Name(), "SpeedLimit")
	}
	if r.CheckSeverity() != "critical" {
		t.Errorf("Severity: got %q, want %q", r.CheckSeverity(), "critical")
	}
}

// AddChecks sends the client's default checks first, then the session's, as
// one setProperties command; the mock's recorded input is read back and
// compared property by property with the serializer's own output.
func TestAddChecks(t *testing.T) {
	speed := CheckSignal("Speed").NeverExceeds(IntRational(220))
	voltage, err := CheckSignal("Voltage").StaysBetween(half(23), half(29))
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	cases := map[string]struct {
		defaults []CheckResult
		session  []CheckResult
		want     []Formula
	}{
		"session only":         {nil, []CheckResult{speed, voltage}, []Formula{speed.Formula(), voltage.Formula()}},
		"default then session": {[]CheckResult{voltage}, []CheckResult{speed}, []Formula{voltage.Formula(), speed.Formula()}},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			mock := NewMockBackend(Respond(`{"status": "success"}`))
			client, err := NewClient(mock, WithDefaultChecks(tc.defaults...))
			if err != nil {
				t.Fatalf("NewClient: %v", err)
			}
			t.Cleanup(func() { _ = client.Close() })
			if err := client.AddChecks(ctx, tc.session); err != nil {
				t.Fatalf("AddChecks: %v", err)
			}
			inputs := mock.Inputs()
			if len(inputs) != 1 {
				t.Fatalf("expected one command, got %d", len(inputs))
			}
			var sent struct {
				Command    string            `json:"command"`
				Properties []json.RawMessage `json:"properties"`
			}
			if err := json.Unmarshal([]byte(inputs[0]), &sent); err != nil {
				t.Fatalf("the command is not JSON: %v", err)
			}
			if sent.Command != "setProperties" {
				t.Errorf("command: got %q, want setProperties", sent.Command)
			}
			if len(sent.Properties) != len(tc.want) {
				t.Fatalf("properties: got %d, want %d", len(sent.Properties), len(tc.want))
			}
			for i, f := range tc.want {
				m, err := serializeFormula(f)
				if err != nil {
					t.Fatalf("serializeFormula: %v", err)
				}
				if got, want := canonicalJSON(t, sent.Properties[i]), canonicalJSON(t, m); got != want {
					t.Errorf("property %d: got %s, want %s", i, got, want)
				}
			}
		})
	}
}

// canonicalJSON re-encodes a JSON value with sorted keys so two encodings of
// the same property compare as strings.
func canonicalJSON(t *testing.T, v any) string {
	t.Helper()
	if raw, ok := v.(json.RawMessage); ok {
		var decoded any
		if err := json.Unmarshal(raw, &decoded); err != nil {
			t.Fatalf("decode: %v", err)
		}
		v = decoded
	}
	out, err := json.Marshal(v)
	if err != nil {
		t.Fatalf("encode: %v", err)
	}
	return string(out)
}

func TestSerializeFormulaDepthLimit(t *testing.T) {
	// nested one level past the serializer's limit
	var f Formula = Atomic{Predicate: Equals{Signal: "S", Value: IntRational(1)}}
	for range maxFormulaDepth + 1 {
		f = Not{Inner: f}
	}
	_, err := serializeFormula(f)
	if err == nil {
		t.Fatal("expected error for deeply nested formula, got nil")
	}
	var aleErr *Error
	if !errors.As(err, &aleErr) {
		t.Fatalf("expected *Error, got %T", err)
	}
	if aleErr.Kind != ErrValidation {
		t.Errorf("kind = %v, want ErrValidation", aleErr.Kind)
	}
}
