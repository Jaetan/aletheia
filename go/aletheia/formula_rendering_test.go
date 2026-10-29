//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"bytes"
	"encoding/json"
	"os"
	"path/filepath"
	"reflect"
	"testing"

	"gopkg.in/yaml.v3"
)

// everyAlternative is the formula docs/FORMULA_RENDERING.yaml holds, built in
// code: every operator of the grammar, every predicate, a change of either
// sign and a time bound in seconds, in milliseconds and in microseconds, a
// binary operator the operand of another.
func everyAlternative() Formula {
	rat := func(n, d int64) Rational { return Rational{Numerator: n, Denominator: d} }
	atom := func(p Predicate) Formula { return Atomic{Predicate: p} }
	eq := atom(Equals{Signal: "Speed", Value: rat(1, 1)})
	lt := atom(LessThan{Signal: "Speed", Value: rat(3, 2)})
	gt := atom(GreaterThan{Signal: "Speed", Value: rat(7, 1)})
	le := atom(LessThanOrEqual{Signal: "Speed", Value: rat(220, 1)})
	ge := atom(GreaterThanOrEqual{Signal: "RPM", Value: rat(0, 1)})
	bt := atom(Between{Signal: "Temp", Min: rat(-40, 1), Max: rat(215, 1)})
	rise := atom(ChangedBy{Signal: "Pos", Delta: rat(5, 2)})
	fall := atom(ChangedBy{Signal: "Neg", Delta: rat(-5, 2)})
	steady := atom(StableWithin{Signal: "Volt", Tolerance: rat(1, 100)})
	// Always(Not(P)) is the shape the printer writes as `never P`.
	neverEq := Always{Inner: Not{Inner: eq}}
	unary := And{Left: Next{Inner: lt}, Right: Or{Left: WeakNext{Inner: gt}, Right: Not{Inner: le}}}
	temporal := Until{Left: Always{Inner: ge}, Right: Release{Left: Eventually{Inner: bt}, Right: rise}}
	// Two seconds, then 1500 microseconds, which is no whole millisecond, then 7.
	metricUntil := MetricUntil{Bound: TimeBound{Microseconds: 2_000_000}, Left: fall, Right: steady}
	metricRelease := MetricRelease{
		Bound: TimeBound{Microseconds: 1500},
		Left:  metricUntil,
		Right: MetricEventually{Bound: TimeBound{Microseconds: 7}, Inner: eq},
	}
	metricAlways := MetricAlways{Bound: TimeBound{Microseconds: 250_000}, Inner: lt}
	return And{
		Left:  And{Left: neverEq, Right: unary},
		Right: Or{Left: temporal, Right: And{Left: metricRelease, Right: metricAlways}},
	}
}

// formulaRendering is docs/FORMULA_RENDERING.yaml: one formula as the wire
// carries it and the text every binding's printer gives it.
type formulaRendering struct {
	Rendering string `yaml:"rendering"`
	Wire      string `yaml:"wire"`
}

// wireTree is a JSON text decoded to its tree, so two writers' key orders
// compare equal.
func wireTree(t *testing.T, text []byte) any {
	t.Helper()
	var tree any
	if err := json.Unmarshal(text, &tree); err != nil {
		t.Fatalf("decode %s: %v", text, err)
	}
	return tree
}

// The binding builds the shared formula in code, so its serialisation is held
// to the shared wire, compared as JSON, and its rendering to the shared text.
func TestTheSharedFormulaSerialisesToTheSharedWireAndRendersTheSharedText(t *testing.T) {
	path := filepath.Join(repoRoot(t), "docs", "FORMULA_RENDERING.yaml")
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("read %s: %v", path, err)
	}
	decoder := yaml.NewDecoder(bytes.NewReader(data))
	decoder.KnownFields(true)
	var contract formulaRendering
	if err := decoder.Decode(&contract); err != nil {
		t.Fatalf("decode %s: %v", path, err)
	}
	f := everyAlternative()
	serialised, err := serializeFormula(f)
	if err != nil {
		t.Fatalf("serialise: %v", err)
	}
	encoded, err := json.Marshal(serialised)
	if err != nil {
		t.Fatalf("encode: %v", err)
	}
	if got, want := wireTree(t, encoded), wireTree(t, []byte(contract.Wire)); !reflect.DeepEqual(got, want) {
		t.Errorf("wire:\n got %s\nwant %s", encoded, contract.Wire)
	}
	rendered, err := formatFormula(f)
	if err != nil {
		t.Fatalf("render: %v", err)
	}
	if rendered != contract.Rendering {
		t.Errorf("rendering:\n got %q\nwant %q", rendered, contract.Rendering)
	}
}
