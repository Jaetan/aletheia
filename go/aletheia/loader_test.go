//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"reflect"
	"strings"
	"testing"
)

// thenBuilder is the trailing half of a when-then check, fresh each time: the
// builders carry what has been said so far, so two calls must not share one.
func thenBuilder() ThenSignalBuilder {
	return CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed")
}

// fixedValues answers every slot with what it holds, or refuses every slot
// with one error. A loader's own refusals are that loader's business, so a
// dispatcher test needs no more than this.
type fixedValues struct {
	value, lo, hi Rational
	withinMs      int64
	err           error
}

func (f fixedValues) Value() (Rational, error)           { return f.value, f.err }
func (f fixedValues) Range() (Rational, Rational, error) { return f.lo, f.hi, f.err }
func (f fixedValues) Within() (int64, error)             { return f.withinMs, f.err }

// Each word the trailing half accepts builds what the same call written by
// hand builds, reading the slots its own condition reads.
func TestDispatchThen_BuildsWhatTheBuilderBuilds(t *testing.T) {
	cases := map[string]struct {
		condition string
		values    fixedValues
		withinMs  int64
		byHand    func() (CheckResult, error)
	}{
		"equals": {
			condition: "equals", values: fixedValues{value: IntRational(1)}, withinMs: 100,
			byHand: func() (CheckResult, error) { return thenBuilder().Equals(IntRational(1)).Within(100) },
		},
		"exceeds": {
			condition: "exceeds", values: fixedValues{value: IntRational(30)}, withinMs: 200,
			byHand: func() (CheckResult, error) { return thenBuilder().Exceeds(IntRational(30)).Within(200) },
		},
		"stays_between": {
			condition: "stays_between", values: fixedValues{lo: IntRational(10), hi: IntRational(90)}, withinMs: 300,
			byHand: func() (CheckResult, error) {
				return thenBuilder().StaysBetween(IntRational(10), IntRational(90)).Within(300)
			},
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			got, err := DispatchThen(thenBuilder(), tc.condition, tc.values, tc.withinMs)
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
	// Every word the table holds is exercised above, so an obligation added
	// with no case here fails rather than going untested.
	for word := range thenBuilders {
		if _, ok := cases[word]; !ok {
			t.Errorf("the trailing half accepts %q and this test has no case for it", word)
		}
	}
}

// A slot a loader cannot answer refuses the build, in that loader's own words
// and unchanged: the dispatcher neither swallows the refusal nor rewrites it.
func TestDispatchers_CarryTheLoadersRefusal(t *testing.T) {
	refusal := errors.New("row 7: the column is empty")
	for word := range thenBuilders {
		t.Run("then/"+word, func(t *testing.T) {
			_, err := DispatchThen(thenBuilder(), word, fixedValues{err: refusal}, 100)
			if !errors.Is(err, refusal) {
				t.Errorf("got %v, want the loader's own refusal", err)
			}
		})
	}
	for word := range simpleBuilders {
		t.Run("simple/"+word, func(t *testing.T) {
			_, err := DispatchSimple("Speed", word, fixedValues{err: refusal})
			if !errors.Is(err, refusal) {
				t.Errorf("got %v, want the loader's own refusal", err)
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
	for word := range whenBuilders {
		if _, ok := cases[word]; !ok {
			t.Errorf("the leading half accepts %q and this test has no case for it", word)
		}
	}
}

// Each word a check may carry on its own builds the check of the same name.
func TestDispatchSimple_BuildsWhatTheBuilderBuilds(t *testing.T) {
	cases := map[string]struct {
		values fixedValues
		byHand func() (CheckResult, error)
	}{
		"never_exceeds": {
			values: fixedValues{value: IntRational(220)},
			byHand: func() (CheckResult, error) { return CheckSignal("Speed").NeverExceeds(IntRational(220)), nil },
		},
		"never_below": {
			values: fixedValues{value: IntRational(220)},
			byHand: func() (CheckResult, error) { return CheckSignal("Speed").NeverBelow(IntRational(220)), nil },
		},
		"never_equals": {
			values: fixedValues{value: IntRational(220)},
			byHand: func() (CheckResult, error) { return CheckSignal("Speed").NeverEquals(IntRational(220)), nil },
		},
		"equals": {
			values: fixedValues{value: IntRational(220)},
			byHand: func() (CheckResult, error) { return CheckSignal("Speed").Equals(IntRational(220)).Always(), nil },
		},
		"stays_between": {
			values: fixedValues{lo: IntRational(1), hi: IntRational(9)},
			byHand: func() (CheckResult, error) {
				return CheckSignal("Speed").StaysBetween(IntRational(1), IntRational(9))
			},
		},
		"settles_between": {
			values: fixedValues{lo: IntRational(1), hi: IntRational(9), withinMs: 500},
			byHand: func() (CheckResult, error) {
				return CheckSignal("Speed").SettlesBetween(IntRational(1), IntRational(9)).Within(500)
			},
		},
	}
	for condition, tc := range cases {
		t.Run(condition, func(t *testing.T) {
			got, err := DispatchSimple("Speed", condition, tc.values)
			if err != nil {
				t.Fatalf("DispatchSimple: %v", err)
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
	for word := range simpleBuilders {
		if _, ok := cases[word]; !ok {
			t.Errorf("a check may carry %q on its own and this test has no case for it", word)
		}
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
			dispatch: func() error { _, err := DispatchSimple("Speed", "flickers", fixedValues{}); return err },
			names:    "unknown simple condition",
		},
		"when": {
			dispatch: func() error { _, err := DispatchWhen(CheckWhen("Brake"), "flickers", IntRational(1)); return err },
			names:    "unknown when condition",
		},
		"then": {
			dispatch: func() error {
				_, err := DispatchThen(thenBuilder(), "flickers", fixedValues{}, 100)
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

// Every word the vocabulary accepts reaches a loader that builds it, checked
// through the YAML loader, which is the one inside this module.
func TestVocabulary_EveryWordLoads(t *testing.T) {
	simple := map[string]string{
		"never_exceeds":   "checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 220\n",
		"never_below":     "checks:\n  - signal: Speed\n    condition: never_below\n    value: 10\n",
		"never_equals":    "checks:\n  - signal: Speed\n    condition: never_equals\n    value: 10\n",
		"equals":          "checks:\n  - signal: Speed\n    condition: equals\n    value: 10\n",
		"stays_between":   "checks:\n  - signal: Speed\n    condition: stays_between\n    min: 1\n    max: 2\n",
		"settles_between": "checks:\n  - signal: Speed\n    condition: settles_between\n    min: 1\n    max: 2\n    within_ms: 100\n",
	}
	trigger := "  - when:\n      signal: Brake\n      condition: exceeds\n      value: 10\n    within_ms: 100\n    then:\n      signal: Speed\n"
	obligations := map[string]string{
		"equals":        "checks:\n" + trigger + "      condition: equals\n      value: 5\n",
		"exceeds":       "checks:\n" + trigger + "      condition: exceeds\n      value: 5\n",
		"stays_between": "checks:\n" + trigger + "      condition: stays_between\n      min: 1\n      max: 9\n",
	}

	// The rosters come from the vocabulary rather than from this file, so a
	// word added to it with no way to load it fails here, in both directions.
	for _, pair := range []struct {
		leg       string
		words     []string
		documents map[string]string
	}{
		{"a check carries on its own", keysOf(simpleBuilders), simple},
		{"an obligation closes with", keysOf(thenBuilders), obligations},
	} {
		known := map[string]bool{}
		for _, word := range pair.words {
			known[word] = true
			if _, ok := pair.documents[word]; !ok {
				t.Errorf("%s %q and this test has no document using it", pair.leg, word)
			}
		}
		for word := range pair.documents {
			if !known[word] {
				t.Errorf("this test uses %q, which %s is not", word, pair.leg)
			}
		}
		for word, doc := range pair.documents {
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
	}

	// The other direction: a word the vocabulary does not have is refused
	// before any builder is reached.
	if _, err := LoadChecksFromYAML("checks:\n  - signal: Speed\n    condition: flickers\n    value: 1\n"); err == nil {
		t.Error("the loader took a word outside its vocabulary")
	}
}

// keysOf is the words a builder table holds.
func keysOf[V any](table map[string]V) []string {
	words := make([]string, 0, len(table))
	for word := range table {
		words = append(words, word)
	}
	return words
}
