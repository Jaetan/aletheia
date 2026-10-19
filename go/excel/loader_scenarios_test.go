// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package excel

import (
	"bytes"
	"errors"
	"os"
	"path/filepath"
	"reflect"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
	"github.com/xuri/excelize/v2"
	"gopkg.in/yaml.v3"
)

// The Excel half of docs/LOADER_SCENARIOS.yaml, which the four bindings'
// loaders answer alike: each row's number, written as text in the Checks
// sheet's Value cell or the DBC sheet's Factor cell, loads as the rational the
// row gives or is refused with the kernel's kind, code and fields, located at
// the row and the column header, and printed as the row prints it. The YAML
// half is read by the core module's own test, whose reader this one repeats,
// the two modules sharing no test code.

// loaderScenarios is the contract document, read strictly, so that a key the
// schema lacks fails here rather than going unread.
type loaderScenarios struct {
	YAML         []loaderScenario `yaml:"yaml"`
	YAMLWithinMs []loaderScenario `yaml:"yaml_within_ms"`
	Excel        []loaderScenario `yaml:"excel"`
}

// loaderScenario is one row: the sheet, the number as the cell holds it, and
// what the loader answers for it.
type loaderScenario struct {
	Name   string               `yaml:"name"`
	Sheet  string               `yaml:"sheet"`
	Value  string               `yaml:"value"`
	Expect loaderScenarioExpect `yaml:"expect"`
}

// loaderScenarioExpect is either the value the loader reads (a rational, or
// the milliseconds of a YAML within_ms) or a refusal.
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

// readLoaderScenarios reads the contract from the repository this module sits
// in.
func readLoaderScenarios(t *testing.T) loaderScenarios {
	t.Helper()
	path := filepath.Join("..", "..", "docs", "LOADER_SCENARIOS.yaml")
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
	if len(doc.Excel) == 0 {
		t.Fatalf("%s: no excel scenarios", path)
	}
	return doc
}

// expectedRational is the rational a row expects, and false for a refusal row;
// a row that gives a rational and anything else, or a rational that is not two
// numbers, is a mistake in the contract.
func expectedRational(t *testing.T, sc loaderScenario) (aletheia.Rational, bool) {
	t.Helper()
	if sc.Expect.Rational == nil {
		return aletheia.Rational{}, false
	}
	if len(sc.Expect.Rational) != 2 || sc.Expect.Kind != "" || sc.Expect.Milliseconds != nil {
		t.Fatalf("scenario %s: the contract's expect is malformed: %+v", sc.Name, sc.Expect)
	}
	return aletheia.Rational{Numerator: sc.Expect.Rational[0], Denominator: sc.Expect.Rational[1]}, true
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
		var e *aletheia.Error
		if !errors.As(err, &e) {
			t.Fatalf("scenario %s: got %T (%v), want *aletheia.Error", sc.Name, err, err)
		}
		if e.Kind != aletheia.ErrValidation {
			t.Errorf("scenario %s: Kind = %v, want %v", sc.Name, e.Kind, aletheia.ErrValidation)
		}
		code, location, key = e.Code, e.Location, e.Key
	case "input_bound_exceeded":
		var e *aletheia.InputBoundExceededError
		if !errors.As(err, &e) {
			t.Fatalf("scenario %s: got %T (%v), want *aletheia.InputBoundExceededError", sc.Name, err, err)
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

// makeScenarioWorkbook writes the contract's one data row for the row's sheet
// under that sheet's header row, every cell text but the DBC sheet's Signed
// cell, a boolean false, and the row's number in the Value or Factor cell.
func makeScenarioWorkbook(t *testing.T, sc loaderScenario) string {
	t.Helper()
	var headers []string
	var cells []any
	switch sc.Sheet {
	case "Checks":
		headers = checksHeaders
		cells = []any{"C", "Speed", "never_exceeds", sc.Value}
	case "DBC":
		headers = dbcHeaders
		cells = []any{"256", "M", nil, "8", "Sig", "0", "8", "little_endian", false, sc.Value, "0", "0", "1"}
	default:
		t.Fatalf("scenario %s: the contract names the sheet %q", sc.Name, sc.Sheet)
	}
	f := excelize.NewFile()
	defer f.Close()
	if err := f.SetSheetName("Sheet1", sc.Sheet); err != nil {
		t.Fatal(err)
	}
	write := func(col, row int, v any) {
		cell, err := excelize.CoordinatesToCellName(col, row)
		if err != nil {
			t.Fatal(err)
		}
		if err := f.SetCellValue(sc.Sheet, cell, v); err != nil {
			t.Fatal(err)
		}
	}
	for i, h := range headers {
		write(i+1, 1, h)
	}
	for i, v := range cells {
		if v != nil {
			write(i+1, 2, v)
		}
	}
	path := filepath.Join(t.TempDir(), "scenario.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	return path
}

// Each row's number loads as the check the builder makes around the row's
// rational, or as the signal's factor, or is refused as the row says.
func TestLoaderScenarios_Excel(t *testing.T) {
	for _, sc := range readLoaderScenarios(t).Excel {
		t.Run(sc.Name, func(t *testing.T) {
			path := makeScenarioWorkbook(t, sc)
			want, isRational := expectedRational(t, sc)
			if sc.Sheet == "Checks" {
				checks, err := LoadChecks(path)
				if !isRational {
					requireLoaderRefusal(t, sc, err)
					return
				}
				if err != nil {
					t.Fatalf("scenario %s: %s was refused: %v", sc.Name, sc.Value, err)
				}
				if len(checks) != 1 {
					t.Fatalf("scenario %s: the workbook carried %d checks, want one", sc.Name, len(checks))
				}
				if got, built := checks[0].Formula(), aletheia.CheckSignal("Speed").NeverExceeds(want).Formula(); !reflect.DeepEqual(got, built) {
					t.Errorf("scenario %s: the loaded check is %#v, want %#v", sc.Name, got, built)
				}
				return
			}
			dbc, err := LoadDbc(path)
			if !isRational {
				requireLoaderRefusal(t, sc, err)
				return
			}
			if err != nil {
				t.Fatalf("scenario %s: %s was refused: %v", sc.Name, sc.Value, err)
			}
			if len(dbc.Messages) != 1 || len(dbc.Messages[0].Signals) != 1 {
				t.Fatalf("scenario %s: the workbook carried %d messages, want one of one signal", sc.Name, len(dbc.Messages))
			}
			if got := dbc.Messages[0].Signals[0].Factor; got != want {
				t.Errorf("scenario %s: the factor is %+v, want %+v", sc.Name, got, want)
			}
		})
	}
}
