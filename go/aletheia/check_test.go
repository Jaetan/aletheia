//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"errors"
	"math"
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

func half(n int64) Rational { return ratOf(n, 2) }

// built carries a builder's answer in the deferred shape the tables use.
func built(r CheckResult, err error) func() (CheckResult, error) {
	return func() (CheckResult, error) { return r, err }
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
			built(CheckSignal("Voltage").StaysBetween(half(23), half(29))),
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
				return CheckSignal("Temp").SettlesBetween(IntRational(60), IntRational(80)).Within(TimeBound{Microseconds: 500_000})
			},
			"always within 500ms (60 <= Temp <= 80)",
			must(AlwaysWithin(TimeBound{Microseconds: 500_000},
				Atomic{Predicate: Between{Signal: "Temp", Min: IntRational(60), Max: IntRational(80)}})),
		},
		{
			"when exceeds then equals within",
			func() (CheckResult, error) {
				return CheckWhen("Brake").Exceeds(IntRational(50)).Then("BrakeLight").Equals(IntRational(1)).Within(TimeBound{Microseconds: 100_000})
			},
			"always(not(Brake > 50) or eventually within 100ms (BrakeLight = 1))",
			nil,
		},
		{
			"when drops below then equals within",
			func() (CheckResult, error) {
				return CheckWhen("Voltage").DropsBelow(IntRational(11)).Then("Warning").Equals(IntRational(1)).Within(TimeBound{Microseconds: 50_000})
			},
			"always(not(Voltage < 11) or eventually within 50ms (Warning = 1))",
			nil,
		},
		{
			"when equals then exceeds within",
			func() (CheckResult, error) {
				return CheckWhen("Ignition").Equals(IntRational(1)).Then("FuelPump").Exceeds(IntRational(0)).Within(TimeBound{Microseconds: 50_000})
			},
			"always(not(Ignition = 1) or eventually within 50ms (FuelPump > 0))",
			nil,
		},
		{
			"when exceeds then stays between within",
			func() (CheckResult, error) {
				return CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed").StaysBetween(IntRational(0), IntRational(10)).Within(TimeBound{Microseconds: 200_000})
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

// An inverted range is refused by the kernel's property check where the
// chain finishes, Within for the two chains that defer it, with the reason
// set_properties gives and the code of a property checked on its own.
func TestCheckInvertedRanges(t *testing.T) {
	cases := map[string]func() error{
		"stays between": func() error {
			_, err := CheckSignal("Voltage").StaysBetween(IntRational(5), IntRational(1))
			return err
		},
		"settles between within": func() error {
			_, err := CheckSignal("Temp").SettlesBetween(IntRational(5), IntRational(1)).Within(TimeBound{Microseconds: 500_000})
			return err
		},
		"when then stays between within": func() error {
			_, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed").StaysBetween(IntRational(5), IntRational(1)).Within(TimeBound{Microseconds: 200_000})
			return err
		},
	}
	for name, build := range cases {
		t.Run(name, func(t *testing.T) {
			requireRefused(t, build(), CodeHandlerPropertyRefused, "between: min 5 exceeds max 1")
		})
	}
}

// A range whose two bounds are equal is ordered, in each chain that takes one.
func TestCheckEqualBoundsAreOrdered(t *testing.T) {
	five := IntRational(5)
	if _, err := CheckSignal("Voltage").StaysBetween(five, five); err != nil {
		t.Errorf("stays between: %v", err)
	}
	if _, err := CheckSignal("Temp").SettlesBetween(five, five).Within(TimeBound{Microseconds: 500_000}); err != nil {
		t.Errorf("settles between: %v", err)
	}
	if _, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed").StaysBetween(five, five).Within(TimeBound{Microseconds: 200_000}); err != nil {
		t.Errorf("when then stays between: %v", err)
	}
}

// A time bound of zero, which checks only the current step, and the largest
// the kernel reads, 2^64-1 microseconds, are accepted by both Within chains.
func TestCheckWithinBounds(t *testing.T) {
	chains := map[string]func(TimeBound) error{
		"settles": func(bound TimeBound) error {
			_, err := CheckSignal("T").SettlesBetween(IntRational(0), IntRational(1)).Within(bound)
			return err
		},
		"causal": func(bound TimeBound) error {
			_, err := CheckWhen("A").Exceeds(IntRational(0)).Then("B").Equals(IntRational(1)).Within(bound)
			return err
		},
	}
	for name, within := range chains {
		if err := within(TimeBound{}); err != nil {
			t.Errorf("%s: a zero bound was refused: %v", name, err)
		}
		if err := within(TimeBound{Microseconds: math.MaxUint64}); err != nil {
			t.Errorf("%s: the largest bound was refused: %v", name, err)
		}
	}
}

// The kernel orders a range's bounds exactly: these operands make the naive
// int64 cross products wrap, and the order still comes out right both ways.
func TestCheckStaysBetweenLargeOperands(t *testing.T) {
	lo := ratOf(math.MaxInt64, 2)
	hi := ratOf(math.MaxInt64/2+1, 1)
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
	causal, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("Light").Equals(IntRational(1)).Within(TimeBound{Microseconds: 100_000})
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	cases := []struct {
		check  CheckResult
		signal SignalName
		desc   string
	}{
		{must(CheckSignal("Speed").NeverExceeds(IntRational(220))), "Speed", "<= 220"},
		{must(CheckSignal("V").NeverBelow(half(23))), "V", ">= 11.5"},
		{must(CheckSignal("E").NeverEquals(IntRational(0))), "E", "!= 0"},
		{must(CheckSignal("X").NeverExceeds(IntRational(1000000))), "X", "<= 1000000"},
		{causal, "Light", "= 1 within 100000µs"},
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
	r := must(CheckSignal("Speed").NeverExceeds(IntRational(220))).Named("SpeedLimit").Severity("critical")
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
	ctx := t.Context()
	speed := must(CheckSignal("Speed").NeverExceeds(IntRational(220)))
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

// The depth limit counts every operator, unary and binary alike: a formula
// whose atom sits exactly at the limit serializes, and one a level deeper is
// refused, down either side of a binary operator.
func TestSerializeFormulaDepthLimit_CountsEveryOperator(t *testing.T) {
	atom := Atomic{Predicate: Equals{Signal: "S", Value: IntRational(1)}}
	nest := map[string]func(Formula) Formula{
		"not":          func(f Formula) Formula { return Not{Inner: f} },
		"and on left":  func(f Formula) Formula { return And{Left: f, Right: atom} },
		"or on right":  func(f Formula) Formula { return Or{Left: atom, Right: f} },
		"metric until": func(f Formula) Formula { return MetricUntil{Bound: TimeBound{Microseconds: 1}, Left: f, Right: atom} },
	}
	for name, wrap := range nest {
		t.Run(name, func(t *testing.T) {
			var f Formula = atom
			for range maxFormulaDepth {
				f = wrap(f)
			}
			if _, err := serializeFormula(f); err != nil {
				t.Errorf("an atom at depth %d was refused: %v", maxFormulaDepth, err)
			}
			if _, err := serializeFormula(wrap(f)); err == nil {
				t.Errorf("an atom at depth %d was accepted", maxFormulaDepth+1)
			}
		})
	}
}

// Each operator serializes to the shape the kernel's parser reads, its
// operands in place and a metric operator's bound beside them; a bound of
// zero, which checks only the current step, is carried.
func TestSerializeFormula_OperatorShapes(t *testing.T) {
	a := Atomic{Predicate: LessThan{Signal: "A", Value: IntRational(1)}}
	b := Atomic{Predicate: GreaterThan{Signal: "B", Value: IntRational(2)}}
	wa := `{"operator":"atomic","predicate":{"predicate":"lessThan","signal":"A","value":1}}`
	wb := `{"operator":"atomic","predicate":{"predicate":"greaterThan","signal":"B","value":2}}`
	zero := TimeBound{}
	cases := map[string]struct {
		f    Formula
		want string
	}{
		"and":               {And{Left: a, Right: b}, `{"left":` + wa + `,"operator":"and","right":` + wb + `}`},
		"or":                {Or{Left: a, Right: b}, `{"left":` + wa + `,"operator":"or","right":` + wb + `}`},
		"until":             {Until{Left: a, Right: b}, `{"left":` + wa + `,"operator":"until","right":` + wb + `}`},
		"release":           {Release{Left: a, Right: b}, `{"left":` + wa + `,"operator":"release","right":` + wb + `}`},
		"metric until":      {MetricUntil{Bound: TimeBound{Microseconds: 7}, Left: a, Right: b}, `{"left":` + wa + `,"operator":"metricUntil","right":` + wb + `,"timebound":7}`},
		"metric release":    {MetricRelease{Bound: zero, Left: a, Right: b}, `{"left":` + wa + `,"operator":"metricRelease","right":` + wb + `,"timebound":0}`},
		"metric always":     {MetricAlways{Bound: zero, Inner: a}, `{"formula":` + wa + `,"operator":"metricAlways","timebound":0}`},
		"metric eventually": {MetricEventually{Bound: TimeBound{Microseconds: 3}, Inner: b}, `{"formula":` + wb + `,"operator":"metricEventually","timebound":3}`},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			m, err := serializeFormula(tc.f)
			if err != nil {
				t.Fatalf("serializeFormula: %v", err)
			}
			if got := canonicalJSON(t, m); got != tc.want {
				t.Errorf("got  %s\nwant %s", got, tc.want)
			}
		})
	}
}

// The kernel's property check refuses a predicate's rational whose
// denominator is zero, a between whose minimum is above its maximum and a
// negative stable-within tolerance, naming the predicate and the field; the
// serializer writes the accepted edges, a between whose bounds are equal and
// a tolerance of zero, which allows no change at all, in the kernel's shape.
func TestSerializePredicate_RationalEdges(t *testing.T) {
	zeroDen := ratOf(1, 0)
	refused := map[string]struct {
		p      Predicate
		reason string
	}{
		"equals over zero":      {Equals{Signal: "S", Value: zeroDen}, "equals: value denominator 0 is not positive"},
		"between min over zero": {Between{Signal: "S", Min: zeroDen, Max: IntRational(1)}, "between: min denominator 0 is not positive"},
		"between max over zero": {Between{Signal: "S", Min: IntRational(0), Max: zeroDen}, "between: max denominator 0 is not positive"},
		"tolerance over zero":   {StableWithin{Signal: "S", Tolerance: zeroDen}, "stableWithin: tolerance denominator 0 is not positive"},
		"negative tolerance":    {StableWithin{Signal: "S", Tolerance: IntRational(-1)}, "stableWithin: tolerance -1 is negative"},
		"between inverted":      {Between{Signal: "S", Min: IntRational(2), Max: IntRational(1)}, "between: min 2 exceeds max 1"},
	}
	for name, tc := range refused {
		t.Run(name, func(t *testing.T) {
			requireRefused(t, checkFormula(Atomic{Predicate: tc.p}), CodeHandlerPropertyRefused, tc.reason)
		})
	}
	accepted := map[string]struct {
		p    Predicate
		want string
	}{
		"equals over one": {Equals{Signal: "S", Value: IntRational(3)}, `{"predicate":"equals","signal":"S","value":3}`},
		"between equal":   {Between{Signal: "S", Min: IntRational(4), Max: IntRational(4)}, `{"max":4,"min":4,"predicate":"between","signal":"S"}`},
		"zero tolerance":  {StableWithin{Signal: "S", Tolerance: IntRational(0)}, `{"predicate":"stableWithin","signal":"S","tolerance":0}`},
	}
	for name, tc := range accepted {
		if err := checkFormula(Atomic{Predicate: tc.p}); err != nil {
			t.Errorf("%s: refused: %v", name, err)
		}
		m, err := serializePredicate(tc.p)
		if err != nil {
			t.Errorf("%s: refused: %v", name, err)
			continue
		}
		if got := canonicalJSON(t, m); got != tc.want {
			t.Errorf("%s: got %s, want %s", name, got, tc.want)
		}
	}
}
