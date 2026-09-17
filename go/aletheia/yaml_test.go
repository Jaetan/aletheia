// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"os"
	"path/filepath"
	"testing"
)

// The YAML check loader: what it builds from each written form, what it
// refuses, and what it does with a path.

// loadOne loads a document that must carry exactly one check, and answers it.
func loadOne(t *testing.T, document string) CheckResult {
	t.Helper()
	checks, err := LoadChecksFromYAML(document)
	if err != nil {
		t.Fatalf("the document was refused: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("the document carried %d checks, want one", len(checks))
	}
	return checks[0]
}

// requireSameFormula holds that a loaded check is the check the builder makes.
func requireSameFormula(t *testing.T, got, want CheckResult) {
	t.Helper()
	if gotText, wantText := FormatFormula(got.Formula()), FormatFormula(want.Formula()); gotText != wantText {
		t.Errorf("the loaded check is %q, want %q", gotText, wantText)
	}
}

// mustCheck is a builder call that can refuse, in a fixture where it does not:
// a refusal here is a mistake in the fixture, and the panic says where.
func mustCheck(r CheckResult, err error) CheckResult {
	if err != nil {
		panic(err)
	}
	return r
}

// halves is a rational over two, for the decimal bounds below.
func halves(n int64) Rational { return Rational{Numerator: n, Denominator: 2} }

// Each written condition builds the check the builder of the same name builds,
// with the decimals parsed exactly rather than rounded.
func TestLoadYAML_SimpleConditions(t *testing.T) {
	cases := map[string]struct {
		document string
		want     func(*testing.T) CheckResult
	}{
		"never exceeds": {
			"checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 220\n",
			func(*testing.T) CheckResult { return CheckSignal("Speed").NeverExceeds(IntRational(220)) },
		},
		"never below, a decimal": {
			"checks:\n  - signal: Voltage\n    condition: never_below\n    value: 11.5\n",
			func(*testing.T) CheckResult { return CheckSignal("Voltage").NeverBelow(halves(23)) },
		},
		"never equals": {
			"checks:\n  - signal: ErrorCode\n    condition: never_equals\n    value: 255\n",
			func(*testing.T) CheckResult { return CheckSignal("ErrorCode").NeverEquals(IntRational(255)) },
		},
		"equals": {
			"checks:\n  - signal: Gear\n    condition: equals\n    value: 0\n",
			func(*testing.T) CheckResult { return CheckSignal("Gear").Equals(IntRational(0)).Always() },
		},
		"stays between, two decimals": {
			"checks:\n  - signal: Voltage\n    condition: stays_between\n    min: 11.5\n    max: 14.5\n",
			func(*testing.T) CheckResult {
				return mustCheck(CheckSignal("Voltage").StaysBetween(halves(23), halves(29)))
			},
		},
		"settles between": {
			"checks:\n  - signal: CoolantTemp\n    condition: settles_between\n    min: 80\n    max: 100\n    within_ms: 5000\n",
			func(*testing.T) CheckResult {
				return mustCheck(CheckSignal("CoolantTemp").SettlesBetween(IntRational(80), IntRational(100)).Within(5000))
			},
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			requireSameFormula(t, loadOne(t, tc.document), tc.want(t))
		})
	}
}

// A document with several checks carries them in the order they are written.
func TestLoadYAML_SeveralChecks(t *testing.T) {
	checks, err := LoadChecksFromYAML(
		"checks:\n" +
			"  - signal: Speed\n    condition: never_exceeds\n    value: 220\n" +
			"  - signal: Voltage\n    condition: stays_between\n    min: 11.5\n    max: 14.5\n")
	if err != nil {
		t.Fatalf("the document was refused: %v", err)
	}
	if len(checks) != 2 {
		t.Fatalf("the document carried %d checks, want two", len(checks))
	}
	requireSameFormula(t, checks[0], CheckSignal("Speed").NeverExceeds(IntRational(220)))
	requireSameFormula(t, checks[1], mustCheck(CheckSignal("Voltage").StaysBetween(halves(23), halves(29))))
}

// A trigger and an obligation build the check the builders of the same names
// build, for every pairing the vocabulary allows.
func TestLoadYAML_WhenThen(t *testing.T) {
	cases := map[string]struct {
		document string
		want     func(*testing.T) CheckResult
	}{
		"exceeds, then equals": {
			"checks:\n  - name: \"Brake response\"\n    when:\n      signal: BrakePedal\n      condition: exceeds\n      value: 50\n" +
				"    then:\n      signal: BrakeLight\n      condition: equals\n      value: 1\n    within_ms: 100\n",
			func(*testing.T) CheckResult {
				return mustCheck(CheckWhen("BrakePedal").Exceeds(IntRational(50)).Then("BrakeLight").Equals(IntRational(1)).Within(100))
			},
		},
		"equals, then exceeds": {
			"checks:\n  - when:\n      signal: Ignition\n      condition: equals\n      value: 1\n" +
				"    then:\n      signal: RPM\n      condition: exceeds\n      value: 500\n    within_ms: 2000\n",
			func(*testing.T) CheckResult {
				return mustCheck(CheckWhen("Ignition").Equals(IntRational(1)).Then("RPM").Exceeds(IntRational(500)).Within(2000))
			},
		},
		"drops below, then stays between": {
			"checks:\n  - when:\n      signal: FuelLevel\n      condition: drops_below\n      value: 10\n" +
				"    then:\n      signal: FuelWarning\n      condition: stays_between\n      min: 1\n      max: 1\n    within_ms: 50\n",
			func(*testing.T) CheckResult {
				return mustCheck(CheckWhen("FuelLevel").DropsBelow(IntRational(10)).Then("FuelWarning").
					StaysBetween(IntRational(1), IntRational(1)).Within(50))
			},
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			requireSameFormula(t, loadOne(t, tc.document), tc.want(t))
		})
	}
}

// The optional name and severity reach the check, in both written forms, and
// are empty when the document does not give them.
func TestLoadYAML_Metadata(t *testing.T) {
	cases := map[string]struct {
		document       string
		name, severity string
	}{
		"a name": {
			"checks:\n  - name: \"Speed limit\"\n    signal: Speed\n    condition: never_exceeds\n    value: 220\n",
			"Speed limit", "",
		},
		"a severity": {
			"checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 220\n    severity: critical\n",
			"", "critical",
		},
		"both": {
			"checks:\n  - name: \"Speed limit\"\n    signal: Speed\n    condition: never_exceeds\n    value: 220\n    severity: warning\n",
			"Speed limit", "warning",
		},
		"neither": {
			"checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 220\n",
			"", "",
		},
		"both, on a trigger and an obligation": {
			"checks:\n  - name: \"Brake response\"\n    when:\n      signal: BrakePedal\n      condition: exceeds\n      value: 50\n" +
				"    then:\n      signal: BrakeLight\n      condition: equals\n      value: 1\n    within_ms: 100\n    severity: safety\n",
			"Brake response", "safety",
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			check := loadOne(t, tc.document)
			if check.Name() != tc.name {
				t.Errorf("the name is %q, want %q", check.Name(), tc.name)
			}
			if check.CheckSeverity() != tc.severity {
				t.Errorf("the severity is %q, want %q", check.CheckSeverity(), tc.severity)
			}
		})
	}
}

// A path is read as a file by both entry points, and a path that names nothing
// is an error from the one that takes only files, where the one that also
// takes text tries to read the path as a document and fails there.
func TestLoadYAML_FromAPath(t *testing.T) {
	document := "checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 220\n"
	path := filepath.Join(t.TempDir(), "checks.yaml")
	if err := os.WriteFile(path, []byte(document), 0o644); err != nil {
		t.Fatalf("write: %v", err)
	}
	loaders := map[string]func(string) ([]CheckResult, error){
		"the loader that also takes text": LoadChecksFromYAML,
		"the loader that takes a file":    LoadChecksFromYAMLFile,
	}
	for name, load := range loaders {
		t.Run(name, func(t *testing.T) {
			checks, err := load(path)
			if err != nil {
				t.Fatalf("the file was refused: %v", err)
			}
			if len(checks) != 1 {
				t.Fatalf("the file carried %d checks, want one", len(checks))
			}
			requireSameFormula(t, checks[0], CheckSignal("Speed").NeverExceeds(IntRational(220)))
		})
	}

	if _, err := LoadChecksFromYAMLFile("/nonexistent/path/checks.yaml"); err == nil {
		t.Error("a path naming nothing was accepted as a file")
	} else {
		requireErrorContains(t, err, "YAML file not found")
	}
	if _, err := LoadChecksFromYAML("/nonexistent/path/checks.yaml"); err == nil {
		t.Error("a path naming nothing was accepted as a document")
	}
}

// Every document the loader refuses is refused with what is wrong with it.
func TestLoadYAML_Refusals(t *testing.T) {
	cases := map[string]struct {
		document string
		says     string
	}{
		"no checks key":             {"signals:\n  - foo\n", "must contain a 'checks' list"},
		"the checks are not a list": {"checks: not_a_list\n", "'checks' field must be a list"},
		"neither a signal nor a trigger": {
			"checks:\n  - name: \"Bad check\"\n    condition: never_exceeds\n    value: 100\n",
			"must have 'signal' or 'when'/'then'",
		},
		"a condition the vocabulary lacks": {
			"checks:\n  - signal: Speed\n    condition: bogus\n    value: 100\n", "unknown condition 'bogus'",
		},
		"no value where one is needed": {
			"checks:\n  - signal: Speed\n    condition: never_exceeds\n", "requires 'value'",
		},
		"no value for an equality": {
			"checks:\n  - signal: Gear\n    condition: equals\n", "requires 'value'",
		},
		"half a range": {
			"checks:\n  - signal: Voltage\n    condition: stays_between\n    max: 14.5\n", "requires 'min' and 'max'",
		},
		"a settling with no range": {
			"checks:\n  - signal: Temp\n    condition: settles_between\n    within_ms: 5000\n", "requires 'min' and 'max'",
		},
		"a settling with no time": {
			"checks:\n  - signal: Temp\n    condition: settles_between\n    min: 80\n    max: 100\n", "requires 'within_ms'",
		},
		"a trigger the vocabulary lacks": {
			"checks:\n  - when:\n      signal: Brake\n      condition: bogus\n      value: 50\n" +
				"    then:\n      signal: BrakeLight\n      condition: equals\n      value: 1\n    within_ms: 100\n",
			"unknown when condition 'bogus'",
		},
		"an obligation the vocabulary lacks": {
			"checks:\n  - when:\n      signal: Brake\n      condition: exceeds\n      value: 50\n" +
				"    then:\n      signal: BrakeLight\n      condition: bogus\n      value: 1\n    within_ms: 100\n",
			"unknown then condition 'bogus'",
		},
		"a trigger with no obligation": {
			"checks:\n  - name: \"Incomplete\"\n    when:\n      signal: Brake\n      condition: exceeds\n      value: 50\n    within_ms: 100\n",
			"must have 'signal' or 'when'/'then'",
		},
		"a trigger and an obligation with no time": {
			"checks:\n  - when:\n      signal: Brake\n      condition: exceeds\n      value: 50\n" +
				"    then:\n      signal: BrakeLight\n      condition: equals\n      value: 1\n",
			"require 'within_ms'",
		},
		"a value that is not a number": {
			"checks:\n  - signal: S\n    condition: never_exceeds\n    value: .nan\n", "not a valid decimal literal",
		},
		"a value past the wire range": {
			"checks:\n  - signal: S\n    condition: never_exceeds\n    value: 99999999999999999999.5\n", "Int64 wire range",
		},
		"a bound that is not a number": {
			"checks:\n  - signal: S\n    condition: settles_between\n    min: 0\n    max: .inf\n    within_ms: 100\n",
			"not a valid decimal literal",
		},
		"a trigger value that is not a number": {
			"checks:\n  - when:\n      signal: A\n      condition: exceeds\n      value: .nan\n" +
				"    then:\n      signal: B\n      condition: equals\n      value: 1\n    within_ms: 100\n",
			"not a valid decimal literal",
		},
		"a list where a value belongs": {
			"checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: [1, 2]\n", "expected a numeric scalar value",
		},
		"a mapping where a value belongs": {
			"checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: {a: 1}\n", "expected a numeric scalar value",
		},
		"a list where a bound belongs": {
			"checks:\n  - signal: Speed\n    condition: stays_between\n    min: [1]\n    max: 2\n", "expected a numeric scalar value",
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			_, err := LoadChecksFromYAML(tc.document)
			requireErrorContains(t, err, tc.says)
		})
	}
}

// A refusal names the check it is about, by its name or by a placeholder.
func TestLoadYAML_RefusalsNameTheCheck(t *testing.T) {
	cases := map[string]struct{ document, says string }{
		"a named check": {
			"checks:\n  - name: \"My Check\"\n    signal: Speed\n    condition: bogus\n    value: 100\n", "check 'My Check'",
		},
		"an unnamed one": {
			"checks:\n  - signal: Speed\n    condition: bogus\n    value: 100\n", "check '<unnamed>'",
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			_, err := LoadChecksFromYAML(tc.document)
			requireErrorContains(t, err, tc.says)
		})
	}
}

// A symbolic link is refused rather than followed, by whichever entry point is
// given it, so that what is read is the path that was passed. Text handed in
// place of a path is unaffected.
func TestLoadYAML_RefusesASymbolicLink(t *testing.T) {
	loaders := map[string]func(string) ([]CheckResult, error){
		"the loader that takes a file":    LoadChecksFromYAMLFile,
		"the loader that also takes text": LoadChecksFromYAML,
	}
	for name, load := range loaders {
		t.Run(name, func(t *testing.T) {
			dir := t.TempDir()
			real := filepath.Join(dir, "real.yaml")
			document := "checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 200\n"
			if err := os.WriteFile(real, []byte(document), 0o644); err != nil {
				t.Fatalf("write: %v", err)
			}
			link := filepath.Join(dir, "link.yaml")
			if err := os.Symlink(real, link); err != nil {
				t.Skip("this filesystem does not allow a symbolic link")
			}
			_, err := load(link)
			requireErrorContains(t, err, "symbolic link")
		})
	}

	checks, err := LoadChecksFromYAML("checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 200\n")
	if err != nil {
		t.Fatalf("a document handed as text was refused: %v", err)
	}
	if len(checks) != 1 {
		t.Errorf("the text carried %d checks, want one", len(checks))
	}
}
