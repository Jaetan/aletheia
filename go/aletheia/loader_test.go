//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"reflect"
	"strings"
	"testing"
)

// thenBuilder is the trailing half of a when-then check, fresh each time: the
// builders carry what has been said so far, so two calls must not share one.
func thenBuilder() ThenSignalBuilder {
	return CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed")
}

// Each word the trailing half accepts builds what the same call written by
// hand builds, with the value slots its own condition reads and the time bound
// it was given.
func TestDispatchThen_BuildsWhatTheBuilderBuilds(t *testing.T) {
	cases := map[string]struct {
		condition     string
		value, lo, hi Rational
		withinMs      int64
		byHand        func() (CheckResult, error)
	}{
		"equals": {
			condition: "equals", value: IntRational(1), withinMs: 100,
			byHand: func() (CheckResult, error) { return thenBuilder().Equals(IntRational(1)).Within(100) },
		},
		"exceeds": {
			condition: "exceeds", value: IntRational(30), withinMs: 200,
			byHand: func() (CheckResult, error) { return thenBuilder().Exceeds(IntRational(30)).Within(200) },
		},
		"stays_between": {
			condition: "stays_between", lo: IntRational(10), hi: IntRational(90), withinMs: 300,
			byHand: func() (CheckResult, error) {
				return thenBuilder().StaysBetween(IntRational(10), IntRational(90)).Within(300)
			},
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			got, err := DispatchThen(thenBuilder(), tc.condition, tc.value, tc.lo, tc.hi, tc.withinMs)
			if err != nil {
				t.Fatalf("DispatchThen: %v", err)
			}
			want, err := tc.byHand()
			if err != nil {
				t.Fatalf("the same call by hand: %v", err)
			}
			if !reflect.DeepEqual(got, want) {
				t.Errorf("got %+v, want %+v", got, want)
			}
		})
	}
}

// Each word the leading half accepts builds the condition of the same name.
func TestDispatchWhen_BuildsWhatTheBuilderBuilds(t *testing.T) {
	when := func() WhenSignalBuilder { return CheckWhen("Brake") }
	cases := map[string]func() WhenCondition{
		"exceeds":     func() WhenCondition { return when().Exceeds(IntRational(50)) },
		"equals":      func() WhenCondition { return when().Equals(IntRational(50)) },
		"drops_below": func() WhenCondition { return when().DropsBelow(IntRational(50)) },
	}
	for condition, byHand := range cases {
		t.Run(condition, func(t *testing.T) {
			got, err := DispatchWhen(when(), condition, IntRational(50))
			if err != nil {
				t.Fatalf("DispatchWhen: %v", err)
			}
			if want := byHand(); !reflect.DeepEqual(got, want) {
				t.Errorf("got %+v, want %+v", got, want)
			}
		})
	}
}

// Each single-value word builds the check of the same name.
func TestDispatchSimple_BuildsWhatTheBuilderBuilds(t *testing.T) {
	cases := map[string]func() CheckResult{
		"never_exceeds": func() CheckResult { return CheckSignal("Speed").NeverExceeds(IntRational(220)) },
		"never_below":   func() CheckResult { return CheckSignal("Speed").NeverBelow(IntRational(220)) },
		"never_equals":  func() CheckResult { return CheckSignal("Speed").NeverEquals(IntRational(220)) },
	}
	for condition, byHand := range cases {
		t.Run(condition, func(t *testing.T) {
			got, err := DispatchSimple("Speed", condition, IntRational(220))
			if err != nil {
				t.Fatalf("DispatchSimple: %v", err)
			}
			if want := byHand(); !reflect.DeepEqual(got, want) {
				t.Errorf("got %+v, want %+v", got, want)
			}
		})
	}
}

// A word outside a leg's vocabulary is refused, and the refusal names which
// leg refused it, since the same word can be valid on another.
func TestDispatchers_RefuseWordsOutsideTheirLeg(t *testing.T) {
	cases := map[string]struct {
		dispatch func() error
		names    string
	}{
		"simple": {
			dispatch: func() error { _, err := DispatchSimple("Speed", "flickers", IntRational(1)); return err },
			names:    "unknown simple condition",
		},
		"when": {
			dispatch: func() error { _, err := DispatchWhen(CheckWhen("Brake"), "flickers", IntRational(1)); return err },
			names:    "unknown when condition",
		},
		"then": {
			dispatch: func() error {
				_, err := DispatchThen(thenBuilder(), "flickers", IntRational(1), Rational{}, Rational{}, 100)
				return err
			},
			names: "unknown then condition",
		},
	}
	for leg, tc := range cases {
		t.Run(leg, func(t *testing.T) {
			err := tc.dispatch()
			if err == nil {
				t.Fatal("an unknown condition was accepted")
			}
			if !strings.Contains(err.Error(), tc.names) {
				t.Errorf("error %q does not name the leg that refused it", err)
			}
		})
	}
}

// Every word the vocabulary accepts reaches a loader that builds it. The three
// with no dispatcher are built by each loader from their own shape, so the
// check is made through the YAML loader, which is the one inside this module.
func TestVocabulary_EveryWordLoads(t *testing.T) {
	documents := map[string]string{
		"never_exceeds":   "checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 220\n",
		"never_below":     "checks:\n  - signal: Speed\n    condition: never_below\n    value: 10\n",
		"never_equals":    "checks:\n  - signal: Speed\n    condition: never_equals\n    value: 10\n",
		"equals":          "checks:\n  - signal: Speed\n    condition: equals\n    value: 10\n",
		"stays_between":   "checks:\n  - signal: Speed\n    condition: stays_between\n    min: 1\n    max: 2\n",
		"settles_between": "checks:\n  - signal: Speed\n    condition: settles_between\n    min: 1\n    max: 2\n    within_ms: 100\n",
	}
	// The roster comes from the vocabulary rather than from this file, so a
	// word added to it with no way to load it fails here.
	vocabulary := map[string]bool{}
	for word := range simpleValueBuilders {
		vocabulary[word] = true
	}
	for _, set := range []map[string]bool{simpleRangeConditions, simpleSettlesConditions, simpleEqualsConditions} {
		for word := range set {
			vocabulary[word] = true
		}
	}
	for word := range vocabulary {
		if _, ok := documents[word]; !ok {
			t.Errorf("the vocabulary has %q and this test has no document using it", word)
		}
	}
	for word := range documents {
		if !vocabulary[word] {
			t.Errorf("this test uses %q, which the vocabulary does not have", word)
		}
	}
	for word, doc := range documents {
		t.Run(word, func(t *testing.T) {
			checks, err := LoadChecksFromYAML(doc)
			if err != nil {
				t.Fatalf("the loader refused a word of its own vocabulary: %v", err)
			}
			if len(checks) != 1 {
				t.Fatalf("got %d checks, want 1", len(checks))
			}
		})
	}
	// The other direction: a word the vocabulary does not have is refused
	// before any builder is reached.
	if _, err := LoadChecksFromYAML("checks:\n  - signal: Speed\n    condition: flickers\n    value: 1\n"); err == nil {
		t.Error("the loader took a word outside its vocabulary")
	}
}
