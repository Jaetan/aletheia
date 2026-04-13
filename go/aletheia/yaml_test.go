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
	want := FormatFormula(CheckSignal("Speed").NeverExceeds(220).Formula())
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
	want := FormatFormula(CheckSignal("Voltage").NeverBelow(11.5).Formula())
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
	reference, err := CheckSignal("Voltage").StaysBetween(11.5, 14.5)
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
	want := FormatFormula(CheckSignal("ErrorCode").NeverEquals(255).Formula())
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
	want := FormatFormula(CheckSignal("Gear").Equals(0).Always().Formula())
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
	expected, _ := CheckSignal("CoolantTemp").SettlesBetween(80, 100).Within(5000)
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
	want0 := FormatFormula(CheckSignal("Speed").NeverExceeds(220).Formula())
	got0 := FormatFormula(checks[0].Formula())
	if got0 != want0 {
		t.Errorf("check[0] formula mismatch: got %q, want %q", got0, want0)
	}
	reference1, err := CheckSignal("Voltage").StaysBetween(11.5, 14.5)
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
	expected, _ := CheckWhen("BrakePedal").Exceeds(50).Then("BrakeLight").Equals(1).Within(100)
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
	expected, _ := CheckWhen("Ignition").Equals(1).Then("RPM").Exceeds(500).Within(2000)
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
	expected, _ := CheckWhen("FuelLevel").DropsBelow(10).Then("FuelWarning").StaysBetween(1, 1).Within(50)
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
	want := FormatFormula(CheckSignal("Speed").NeverExceeds(220).Formula())
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
	reference, err := CheckSignal("Voltage").StaysBetween(11.5, 14.5)
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
