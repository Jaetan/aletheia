//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"bytes"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"testing"

	"gopkg.in/yaml.v3"
)

// The YAML half of docs/LOADER_SCENARIOS.yaml, which the four bindings' loaders
// answer alike: each row's number, written under a check's value key or its
// within_ms key, loads as the rational or the milliseconds the row gives or is
// refused with the kernel's kind, code and fields, located at the check and the
// key, and printed as the row prints it. The Excel half is read by the Excel
// module's own test.

// loaderScenarios is the contract document, read strictly, so that a key the
// schema lacks fails here rather than going unread.
type loaderScenarios struct {
	YAML         []loaderScenario `yaml:"yaml"`
	YAMLWithinMs []loaderScenario `yaml:"yaml_within_ms"`
	Excel        []loaderScenario `yaml:"excel"`
}

// loaderScenario is one row: the number as the document spells it, and what
// the loader answers for it.
type loaderScenario struct {
	Name   string               `yaml:"name"`
	Sheet  string               `yaml:"sheet"`
	Value  string               `yaml:"value"`
	Expect loaderScenarioExpect `yaml:"expect"`
}

// loaderScenarioExpect is either the rational or the milliseconds the loader
// reads, or a refusal.
type loaderScenarioExpect struct {
	Rational     []int64              `yaml:"rational"`
	Milliseconds *int64               `yaml:"milliseconds"`
	Kind         string               `yaml:"kind"`
	Code         string               `yaml:"code"`
	Location     string               `yaml:"location"`
	Key          string               `yaml:"key"`
	Printed      string               `yaml:"printed"`
	Bound        *loaderScenarioBound `yaml:"bound"`
}

// loaderScenarioBound is the typed bound error's fields.
type loaderScenarioBound struct {
	Kind     string `yaml:"kind"`
	Observed uint64 `yaml:"observed"`
	Limit    uint64 `yaml:"limit"`
	Field    string `yaml:"field"`
}

// readLoaderScenarios reads the contract from the repository repoRoot names.
func readLoaderScenarios(t *testing.T) loaderScenarios {
	t.Helper()
	path := filepath.Join(repoRoot(t), "docs", "LOADER_SCENARIOS.yaml")
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	decoder := yaml.NewDecoder(bytes.NewReader(data))
	decoder.KnownFields(true)
	var doc loaderScenarios
	if err := decoder.Decode(&doc); err != nil {
		t.Fatalf("decode %s: %v", path, err)
	}
	if len(doc.YAML) == 0 {
		t.Fatalf("%s: no yaml scenarios", path)
	}
	if len(doc.YAMLWithinMs) == 0 {
		t.Fatalf("%s: no yaml_within_ms scenarios", path)
	}
	return doc
}

// expectedRational is the rational a row expects, and false for a refusal row;
// a row that gives a rational and anything else, or a rational that is not two
// numbers, is a mistake in the contract.
func expectedRational(t *testing.T, sc loaderScenario) (Rational, bool) {
	t.Helper()
	if sc.Expect.Rational == nil {
		return Rational{}, false
	}
	if len(sc.Expect.Rational) != 2 || sc.Expect.Kind != "" || sc.Expect.Milliseconds != nil {
		t.Fatalf("scenario %s: the contract's expect is malformed: %+v", sc.Name, sc.Expect)
	}
	return Rational{Numerator: sc.Expect.Rational[0], Denominator: sc.Expect.Rational[1]}, true
}

// expectedMilliseconds is the time bound a yaml_within_ms row expects, and
// false for a refusal row; a row that gives milliseconds and anything else is
// a mistake in the contract.
func expectedMilliseconds(t *testing.T, sc loaderScenario) (int64, bool) {
	t.Helper()
	if sc.Expect.Milliseconds == nil {
		return 0, false
	}
	if sc.Expect.Rational != nil || sc.Expect.Kind != "" {
		t.Fatalf("scenario %s: the contract's expect is malformed: %+v", sc.Name, sc.Expect)
	}
	return *sc.Expect.Milliseconds, true
}

// requireLoaderRefusal holds that the error is the refusal the row names: the
// kernel's type, kind and code, the bound error's fields, the loader's
// location and key, and the string form the row prints. A refusal row that
// also gives a reading is a mistake in the contract.
func requireLoaderRefusal(t *testing.T, sc loaderScenario, err error) {
	t.Helper()
	want := sc.Expect
	if want.Rational != nil || want.Milliseconds != nil {
		t.Fatalf("scenario %s: the contract's expect is malformed: %+v", sc.Name, want)
	}
	if err == nil {
		t.Fatalf("scenario %s: %s was loaded, want the refusal %q", sc.Name, sc.Value, want.Printed)
	}
	var code, location, key string
	switch want.Kind {
	case "validation":
		var e *Error
		if !errors.As(err, &e) {
			t.Fatalf("scenario %s: got %T (%v), want *Error", sc.Name, err, err)
		}
		if e.Kind != ErrValidation {
			t.Errorf("scenario %s: Kind = %v, want %v", sc.Name, e.Kind, ErrValidation)
		}
		code, location, key = e.Code, e.Location, e.Key
	case "input_bound_exceeded":
		var e *InputBoundExceededError
		if !errors.As(err, &e) {
			t.Fatalf("scenario %s: got %T (%v), want *InputBoundExceededError", sc.Name, err, err)
		}
		if want.Bound == nil {
			t.Fatalf("scenario %s: the contract gives no bound", sc.Name)
		}
		if e.BoundKind != want.Bound.Kind {
			t.Errorf("scenario %s: BoundKind = %q, want %q", sc.Name, e.BoundKind, want.Bound.Kind)
		}
		if e.Observed != want.Bound.Observed {
			t.Errorf("scenario %s: Observed = %d, want %d", sc.Name, e.Observed, want.Bound.Observed)
		}
		if e.Limit != want.Bound.Limit {
			t.Errorf("scenario %s: Limit = %d, want %d", sc.Name, e.Limit, want.Bound.Limit)
		}
		if e.Field != want.Bound.Field {
			t.Errorf("scenario %s: Field = %q, want %q", sc.Name, e.Field, want.Bound.Field)
		}
		code, location, key = e.Code, e.Location, e.Key
	default:
		t.Fatalf("scenario %s: the contract names the kind %q", sc.Name, want.Kind)
	}
	if code != want.Code {
		t.Errorf("scenario %s: Code = %q, want %q", sc.Name, code, want.Code)
	}
	if location != want.Location {
		t.Errorf("scenario %s: Location = %q, want %q", sc.Name, location, want.Location)
	}
	if key != want.Key {
		t.Errorf("scenario %s: Key = %q, want %q", sc.Name, key, want.Key)
	}
	if got := err.Error(); got != want.Printed {
		t.Errorf("scenario %s: Error() = %q, want %q", sc.Name, got, want.Printed)
	}
}

// Each row's number, under the value key of a check named C, loads as the
// check the builder makes around the row's rational, or is refused as the row
// says.
func TestLoaderScenarios_YAML(t *testing.T) {
	for _, sc := range readLoaderScenarios(t).YAML {
		t.Run(sc.Name, func(t *testing.T) {
			document := fmt.Sprintf(
				"checks:\n  - name: \"C\"\n    signal: Speed\n    condition: never_exceeds\n    value: %s\n", sc.Value)
			checks, err := LoadChecksFromYAML(document)
			want, isRational := expectedRational(t, sc)
			if !isRational {
				requireLoaderRefusal(t, sc, err)
				return
			}
			if err != nil {
				t.Fatalf("scenario %s: %s was refused: %v", sc.Name, sc.Value, err)
			}
			if len(checks) != 1 {
				t.Fatalf("scenario %s: the document carried %d checks, want one", sc.Name, len(checks))
			}
			got, built := FormatFormula(checks[0].Formula()), FormatFormula(CheckSignal("Speed").NeverExceeds(want).Formula())
			if got != built {
				t.Errorf("scenario %s: the loaded check is %q, want %q", sc.Name, got, built)
			}
		})
	}
}

// Each yaml_within_ms row's number, under the within_ms key of a check named C
// that settles between 0 and 100, loads as the check the builder makes around
// the row's milliseconds, or is refused as the row says.
func TestLoaderScenarios_YAMLWithinMs(t *testing.T) {
	for _, sc := range readLoaderScenarios(t).YAMLWithinMs {
		t.Run(sc.Name, func(t *testing.T) {
			document := fmt.Sprintf(
				"checks:\n  - name: \"C\"\n    signal: Speed\n    condition: settles_between\n"+
					"    min: 0\n    max: 100\n    within_ms: %s\n", sc.Value)
			checks, err := LoadChecksFromYAML(document)
			want, isReading := expectedMilliseconds(t, sc)
			if !isReading {
				requireLoaderRefusal(t, sc, err)
				return
			}
			if err != nil {
				t.Fatalf("scenario %s: %s was refused: %v", sc.Name, sc.Value, err)
			}
			if len(checks) != 1 {
				t.Fatalf("scenario %s: the document carried %d checks, want one", sc.Name, len(checks))
			}
			built, err := CheckSignal("Speed").SettlesBetween(IntRational(0), IntRational(100)).Within(want)
			if err != nil {
				t.Fatalf("scenario %s: the builder refused %d ms: %v", sc.Name, want, err)
			}
			if got, wantFormula := FormatFormula(checks[0].Formula()), FormatFormula(built.Formula()); got != wantFormula {
				t.Errorf("scenario %s: the loaded check is %q, want %q", sc.Name, got, wantFormula)
			}
		})
	}
}
