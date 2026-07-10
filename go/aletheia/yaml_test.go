// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"os"
	"path/filepath"
	"testing"
)

// ===========================================================================
// Simple checks -- each condition type
// ===========================================================================

func TestLoadYAMLNeverExceeds(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: never_exceeds
    value: 220
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	want := FormatFormula(CheckSignal("Speed").NeverExceeds(IntRational(220)).Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLNeverBelow(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: Voltage
    condition: never_below
    value: 11.5
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	want := FormatFormula(CheckSignal("Voltage").NeverBelow(Rational{Numerator: 23, Denominator: 2}).Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLStaysBetween(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: Voltage
    condition: stays_between
    min: 11.5
    max: 14.5
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	reference, err := CheckSignal("Voltage").StaysBetween(Rational{Numerator: 23, Denominator: 2}, Rational{Numerator: 29, Denominator: 2})
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	want := FormatFormula(reference.Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLNeverEquals(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: ErrorCode
    condition: never_equals
    value: 255
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	want := FormatFormula(CheckSignal("ErrorCode").NeverEquals(IntRational(255)).Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLEquals(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: Gear
    condition: equals
    value: 0
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	want := FormatFormula(CheckSignal("Gear").Equals(IntRational(0)).Always().Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLSettlesBetween(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: CoolantTemp
    condition: settles_between
    min: 80
    max: 100
    within_ms: 5000
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	expected, _ := CheckSignal("CoolantTemp").SettlesBetween(IntRational(80), IntRational(100)).Within(5000)
	want := FormatFormula(expected.Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLMultipleChecks(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: never_exceeds
    value: 220
  - signal: Voltage
    condition: stays_between
    min: 11.5
    max: 14.5
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 2 {
		t.Fatalf("expected 2 checks, got %d", len(checks))
	}
	want0 := FormatFormula(CheckSignal("Speed").NeverExceeds(IntRational(220)).Formula())
	got0 := FormatFormula(checks[0].Formula())
	if got0 != want0 {
		t.Errorf("check[0] formula mismatch: got %q, want %q", got0, want0)
	}
	reference1, err := CheckSignal("Voltage").StaysBetween(Rational{Numerator: 23, Denominator: 2}, Rational{Numerator: 29, Denominator: 2})
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	want1 := FormatFormula(reference1.Formula())
	got1 := FormatFormula(checks[1].Formula())
	if got1 != want1 {
		t.Errorf("check[1] formula mismatch: got %q, want %q", got1, want1)
	}
}

// ===========================================================================
// When/Then checks
// ===========================================================================

func TestLoadYAMLWhenExceedsThenEquals(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - name: "Brake response"
    when:
      signal: BrakePedal
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
    within_ms: 100
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	expected, _ := CheckWhen("BrakePedal").Exceeds(IntRational(50)).Then("BrakeLight").Equals(IntRational(1)).Within(100)
	want := FormatFormula(expected.Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLWhenEqualsThenExceeds(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - when:
      signal: Ignition
      condition: equals
      value: 1
    then:
      signal: RPM
      condition: exceeds
      value: 500
    within_ms: 2000
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	expected, _ := CheckWhen("Ignition").Equals(IntRational(1)).Then("RPM").Exceeds(IntRational(500)).Within(2000)
	want := FormatFormula(expected.Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLWhenDropsBelowThenStaysBetween(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - when:
      signal: FuelLevel
      condition: drops_below
      value: 10
    then:
      signal: FuelWarning
      condition: stays_between
      min: 1
      max: 1
    within_ms: 50
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	expected, _ := CheckWhen("FuelLevel").DropsBelow(IntRational(10)).Then("FuelWarning").StaysBetween(IntRational(1), IntRational(1)).Within(50)
	want := FormatFormula(expected.Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

// ===========================================================================
// Metadata
// ===========================================================================

func TestLoadYAMLNameSet(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - name: "Speed limit"
    signal: Speed
    condition: never_exceeds
    value: 220
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].Name() != "Speed limit" {
		t.Errorf("Name: got %q, want %q", checks[0].Name(), "Speed limit")
	}
}

func TestLoadYAMLSeveritySet(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: never_exceeds
    value: 220
    severity: critical
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].CheckSeverity() != "critical" {
		t.Errorf("Severity: got %q, want %q", checks[0].CheckSeverity(), "critical")
	}
}

func TestLoadYAMLNameAndSeverity(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - name: "Speed limit"
    signal: Speed
    condition: never_exceeds
    value: 220
    severity: warning
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].Name() != "Speed limit" {
		t.Errorf("Name: got %q, want %q", checks[0].Name(), "Speed limit")
	}
	if checks[0].CheckSeverity() != "warning" {
		t.Errorf("Severity: got %q, want %q", checks[0].CheckSeverity(), "warning")
	}
}

func TestLoadYAMLDefaultsEmpty(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: never_exceeds
    value: 220
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].Name() != "" {
		t.Errorf("Name: got %q, want empty", checks[0].Name())
	}
	if checks[0].CheckSeverity() != "" {
		t.Errorf("Severity: got %q, want empty", checks[0].CheckSeverity())
	}
}

func TestLoadYAMLWhenThenMetadata(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - name: "Brake response"
    when:
      signal: BrakePedal
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
    within_ms: 100
    severity: safety
`)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].Name() != "Brake response" {
		t.Errorf("Name: got %q, want %q", checks[0].Name(), "Brake response")
	}
	if checks[0].CheckSeverity() != "safety" {
		t.Errorf("Severity: got %q, want %q", checks[0].CheckSeverity(), "safety")
	}
}

// ===========================================================================
// File I/O
// ===========================================================================

func TestLoadYAMLFromFile(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "checks.yaml")
	content := `checks:
  - signal: Speed
    condition: never_exceeds
    value: 220
`
	if err := os.WriteFile(path, []byte(content), 0644); err != nil {
		t.Fatal(err)
	}
	checks, err := LoadChecksFromYAML(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	want := FormatFormula(CheckSignal("Speed").NeverExceeds(IntRational(220)).Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLFileNotFound(t *testing.T) {
	// When the file doesn't exist, LoadChecksFromYAML treats it as inline YAML,
	// which fails during parsing. Use LoadChecksFromYAMLFile for explicit file errors.
	_, err := LoadChecksFromYAML("/nonexistent/path/checks.yaml")
	if err == nil {
		t.Fatal("expected error for non-existent path treated as inline YAML")
	}
}

func TestLoadYAMLFromFileFunc(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "checks.yaml")
	content := `checks:
  - signal: Voltage
    condition: stays_between
    min: 11.5
    max: 14.5
`
	if err := os.WriteFile(path, []byte(content), 0644); err != nil {
		t.Fatal(err)
	}
	checks, err := LoadChecksFromYAMLFile(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	reference, err := CheckSignal("Voltage").StaysBetween(Rational{Numerator: 23, Denominator: 2}, Rational{Numerator: 29, Denominator: 2})
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	want := FormatFormula(reference.Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLFileNotFoundFunc(t *testing.T) {
	_, err := LoadChecksFromYAMLFile("/nonexistent/path/checks.yaml")
	requireErrorContains(t, err, "YAML file not found")
}

// ===========================================================================
// Error handling
// ===========================================================================

func TestLoadYAMLMissingChecksKey(t *testing.T) {
	_, err := LoadChecksFromYAML("signals:\n  - foo\n")
	requireErrorContains(t, err, "YAML document must contain a 'checks' list")
}

func TestLoadYAMLChecksNotList(t *testing.T) {
	_, err := LoadChecksFromYAML("checks: not_a_list\n")
	requireErrorContains(t, err, "YAML 'checks' field must be a list")
}

func TestLoadYAMLNoSignalOrWhen(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - name: "Bad check"
    condition: never_exceeds
    value: 100
`)
	requireErrorContains(t, err, "must have 'signal' or 'when'/'then'")
}

func TestLoadYAMLUnknownCondition(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: bogus
    value: 100
`)
	requireErrorContains(t, err, "unknown condition 'bogus'")
}

func TestLoadYAMLMissingValue(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: never_exceeds
`)
	requireErrorContains(t, err, "requires 'value'")
}

// TestLoadYAMLRejectsNonFiniteValue is the regression test for the silent-clamp
// bug: a non-decimal (`.nan` / `.inf`) or int64-overflowing value in a check
// file must make the loader FAIL (matching the Python / C++ / Rust loaders), not
// silently clamp to 0/1. Under the decimal SSOT the literal text is parsed by the
// kernel FromDecimal, so `.nan` / `.inf` are rejected as invalid decimal
// literals and a too-large value as an Int64-wire overflow. Covers the simple,
// settles, and when/then dispatch paths.
func TestLoadYAMLRejectsNonFiniteValue(t *testing.T) {
	cases := []struct {
		name, yaml, want string
	}{
		{
			name: "simple NaN",
			yaml: "checks:\n  - signal: S\n    condition: never_exceeds\n    value: .nan\n",
			want: "not a valid decimal literal",
		},
		{
			name: "simple overflow",
			yaml: "checks:\n  - signal: S\n    condition: never_exceeds\n    value: 99999999999999999999.5\n",
			want: "Int64 wire range",
		},
		{
			name: "settles Inf bound",
			yaml: "checks:\n  - signal: S\n    condition: settles_between\n    min: 0\n    max: .inf\n    within_ms: 100\n",
			want: "not a valid decimal literal",
		},
		{
			name: "when-clause NaN",
			yaml: "checks:\n  - when:\n      signal: A\n      condition: exceeds\n      value: .nan\n    then:\n      signal: B\n      condition: equals\n      value: 1\n    within_ms: 100\n",
			want: "not a valid decimal literal",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			_, err := LoadChecksFromYAML(tc.yaml)
			requireErrorContains(t, err, tc.want)
		})
	}
}

func TestLoadYAMLStaysBetweenMissingRange(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Voltage
    condition: stays_between
    max: 14.5
`)
	requireErrorContains(t, err, "requires 'min' and 'max'")
}

func TestLoadYAMLSettlesMissingWithin(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Temp
    condition: settles_between
    min: 80
    max: 100
`)
	requireErrorContains(t, err, "requires 'within_ms'")
}

func TestLoadYAMLSettlesMissingRange(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Temp
    condition: settles_between
    within_ms: 5000
`)
	requireErrorContains(t, err, "requires 'min' and 'max'")
}

func TestLoadYAMLEqualsMissingValue(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Gear
    condition: equals
`)
	requireErrorContains(t, err, "requires 'value'")
}

func TestLoadYAMLUnknownWhenCondition(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - when:
      signal: Brake
      condition: bogus
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
    within_ms: 100
`)
	requireErrorContains(t, err, "unknown when condition 'bogus'")
}

func TestLoadYAMLUnknownThenCondition(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - when:
      signal: Brake
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: bogus
      value: 1
    within_ms: 100
`)
	requireErrorContains(t, err, "unknown then condition 'bogus'")
}

func TestLoadYAMLNamedCheckInError(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - name: "My Check"
    signal: Speed
    condition: bogus
    value: 100
`)
	requireErrorContains(t, err, "check 'My Check'")
}

func TestLoadYAMLUnnamedCheckInError(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: bogus
    value: 100
`)
	requireErrorContains(t, err, "check '<unnamed>'")
}

func TestLoadYAMLWhenThenMissingThen(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - name: "Incomplete"
    when:
      signal: Brake
      condition: exceeds
      value: 50
    within_ms: 100
`)
	requireErrorContains(t, err, "must have 'signal' or 'when'/'then'")
}

func TestLoadYAMLWhenThenMissingWithinMs(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - when:
      signal: Brake
      condition: exceeds
      value: 50
    then:
      signal: BrakeLight
      condition: equals
      value: 1
`)
	requireErrorContains(t, err, "require 'within_ms'")
}

// ===========================================================================
// Adversarial-input hardening (cross-binding mirror)
// ===========================================================================

func TestLoadChecksFromYAMLFile_RejectsSymlink(t *testing.T) {
	tmp := t.TempDir()
	real_ := filepath.Join(tmp, "real.yaml")
	if err := os.WriteFile(real_, []byte("checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 200\n"), 0o644); err != nil {
		t.Fatalf("write: %v", err)
	}
	link := filepath.Join(tmp, "link.yaml")
	if err := os.Symlink(real_, link); err != nil {
		t.Skip("symlink creation not permitted on this filesystem")
	}
	_, err := LoadChecksFromYAMLFile(link)
	requireErrorContains(t, err, "symbolic link")
}

func TestLoadChecksFromYAML_AutoDetectRejectsSymlink(t *testing.T) {
	tmp := t.TempDir()
	real_ := filepath.Join(tmp, "real_auto.yaml")
	if err := os.WriteFile(real_, []byte("checks:\n  - signal: Speed\n    condition: never_exceeds\n    value: 200\n"), 0o644); err != nil {
		t.Fatalf("write: %v", err)
	}
	link := filepath.Join(tmp, "link_auto.yaml")
	if err := os.Symlink(real_, link); err != nil {
		t.Skip("symlink creation not permitted on this filesystem")
	}
	// LoadChecksFromYAML auto-detects: when source resolves to an existing
	// path, it goes through the file branch (which now rejects symlinks).
	_, err := LoadChecksFromYAML(link)
	requireErrorContains(t, err, "symbolic link")
}

func TestLoadChecksFromYAML_InlineStringUnaffected(t *testing.T) {
	checks, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: never_exceeds
    value: 200
`)
	if err != nil {
		t.Fatalf("inline YAML rejected: %v", err)
	}
	if len(checks) != 1 {
		t.Errorf("checks: got %d, want 1", len(checks))
	}
}
