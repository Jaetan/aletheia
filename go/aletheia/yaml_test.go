package aletheia

import (
	"os"
	"path/filepath"
	"strings"
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
	want := FormatFormula(CheckSignal("Voltage").StaysBetween(11.5, 14.5).Formula())
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
	want1 := FormatFormula(CheckSignal("Voltage").StaysBetween(11.5, 14.5).Formula())
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
	_, err := LoadChecksFromYAML("/nonexistent/path/checks.yaml")
	if err == nil {
		t.Fatal("expected error for non-existent file")
	}
	if !strings.Contains(err.Error(), "YAML file not found") {
		t.Errorf("error message should contain 'YAML file not found', got: %v", err)
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
	want := FormatFormula(CheckSignal("Voltage").StaysBetween(11.5, 14.5).Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadYAMLFileNotFoundFunc(t *testing.T) {
	_, err := LoadChecksFromYAMLFile("/nonexistent/path/checks.yaml")
	if err == nil {
		t.Fatal("expected error for non-existent file")
	}
	if !strings.Contains(err.Error(), "YAML file not found") {
		t.Errorf("error message should contain 'YAML file not found', got: %v", err)
	}
}

// ===========================================================================
// Error handling
// ===========================================================================

func TestLoadYAMLMissingChecksKey(t *testing.T) {
	_, err := LoadChecksFromYAML("signals:\n  - foo\n")
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "YAML must contain a 'checks' list") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLChecksNotList(t *testing.T) {
	_, err := LoadChecksFromYAML("checks: not_a_list\n")
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "YAML must contain a 'checks' list") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLNoSignalOrWhen(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - name: "Bad check"
    condition: never_exceeds
    value: 100
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "must have 'signal' or 'when'/'then'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLUnknownCondition(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: bogus
    value: 100
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "unknown condition 'bogus'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLMissingValue(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: never_exceeds
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "requires 'value'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLStaysBetweenMissingRange(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Voltage
    condition: stays_between
    max: 14.5
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "requires 'min' and 'max'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLSettlesMissingWithin(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Temp
    condition: settles_between
    min: 80
    max: 100
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "requires 'within_ms'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLSettlesMissingRange(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Temp
    condition: settles_between
    within_ms: 5000
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "requires 'min' and 'max'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLEqualsMissingValue(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Gear
    condition: equals
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "requires 'value'") {
		t.Errorf("unexpected error: %v", err)
	}
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
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "unknown when condition 'bogus'") {
		t.Errorf("unexpected error: %v", err)
	}
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
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "unknown then condition 'bogus'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadYAMLNamedCheckInError(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - name: "My Check"
    signal: Speed
    condition: bogus
    value: 100
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "Check 'My Check'") {
		t.Errorf("error should contain check name, got: %v", err)
	}
}

func TestLoadYAMLUnnamedCheckInError(t *testing.T) {
	_, err := LoadChecksFromYAML(`
checks:
  - signal: Speed
    condition: bogus
    value: 100
`)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "Check '<unnamed>'") {
		t.Errorf("error should contain '<unnamed>', got: %v", err)
	}
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
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "must have 'signal' or 'when'/'then'") {
		t.Errorf("unexpected error: %v", err)
	}
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
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "require 'within_ms'") {
		t.Errorf("unexpected error: %v", err)
	}
}
