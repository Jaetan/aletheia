// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"testing"
)

// mustDesc renders a CheckResult's condition description, failing the test on a
// renderer error. ConditionDesc renders thresholds via the kernel formatℚ, so it
// needs the GHC runtime up — TestMain (main_test.go) brings it up package-wide.
func mustDesc(t *testing.T, r CheckResult) string {
	t.Helper()
	s, err := r.ConditionDesc()
	if err != nil {
		t.Fatalf("ConditionDesc: %v", err)
	}
	return s
}

// ===========================================================================
// One-shot methods
// ===========================================================================

func TestCheckSignalNeverExceeds(t *testing.T) {
	r := CheckSignal("Speed").NeverExceeds(IntRational(220))
	got := FormatFormula(r.Formula())
	want := "always(Speed <= 220)"
	if got != want {
		t.Errorf("NeverExceeds: got %q, want %q", got, want)
	}
}

func TestCheckSignalNeverBelow(t *testing.T) {
	r := CheckSignal("Voltage").NeverBelow(Rational{Numerator: 23, Denominator: 2})
	got := FormatFormula(r.Formula())
	want := "always(Voltage >= 11.5)"
	if got != want {
		t.Errorf("NeverBelow: got %q, want %q", got, want)
	}
}

func TestCheckSignalStaysBetween(t *testing.T) {
	r, err := CheckSignal("Voltage").StaysBetween(Rational{Numerator: 23, Denominator: 2}, Rational{Numerator: 29, Denominator: 2})
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always(11.5 <= Voltage <= 14.5)"
	if got != want {
		t.Errorf("StaysBetween: got %q, want %q", got, want)
	}
}

func TestCheckSignalStaysBetweenInverted(t *testing.T) {
	_, err := CheckSignal("Voltage").StaysBetween(Rational{Numerator: 29, Denominator: 2}, Rational{Numerator: 23, Denominator: 2})
	if err == nil {
		t.Fatal("expected error for inverted range")
	}
}

func TestCheckSignalSettlesBetweenInverted(t *testing.T) {
	_, err := CheckSignal("Temp").SettlesBetween(IntRational(80), IntRational(60)).Within(500)
	if err == nil {
		t.Fatal("expected error for inverted range")
	}
}

func TestCheckWhenThenStaysBetweenInverted(t *testing.T) {
	_, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed").StaysBetween(IntRational(10), IntRational(0)).Within(200)
	if err == nil {
		t.Fatal("expected error for inverted range")
	}
}

func TestCheckSignalNeverEquals(t *testing.T) {
	r := CheckSignal("ErrorCode").NeverEquals(IntRational(255))
	got := FormatFormula(r.Formula())
	want := "never ErrorCode = 255"
	if got != want {
		t.Errorf("NeverEquals: got %q, want %q", got, want)
	}
}

// ===========================================================================
// Two-step methods
// ===========================================================================

func TestCheckSignalEqualsAlways(t *testing.T) {
	r := CheckSignal("Gear").Equals(IntRational(0)).Always()
	got := FormatFormula(r.Formula())
	want := "always(Gear = 0)"
	if got != want {
		t.Errorf("Equals.Always: got %q, want %q", got, want)
	}
}

func TestCheckSignalSettlesBetweenWithin(t *testing.T) {
	r, err := CheckSignal("Temp").SettlesBetween(IntRational(60), IntRational(80)).Within(500)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always within 500ms (60 <= Temp <= 80)"
	if got != want {
		t.Errorf("SettlesBetween.Within: got %q, want %q", got, want)
	}
}

// ===========================================================================
// Causal chains (when/then)
// ===========================================================================

func TestCheckWhenThenEqualsWithin(t *testing.T) {
	r, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("BrakeLight").Equals(IntRational(1)).Within(100)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always(not(Brake > 50) or eventually within 100ms (BrakeLight = 1))"
	if got != want {
		t.Errorf("When.Then.Equals.Within: got %q, want %q", got, want)
	}
}

func TestCheckWhenDropsBelowThenWithin(t *testing.T) {
	r, err := CheckWhen("Voltage").DropsBelow(IntRational(11)).Then("Warning").Equals(IntRational(1)).Within(50)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always(not(Voltage < 11) or eventually within 50ms (Warning = 1))"
	if got != want {
		t.Errorf("DropsBelow.Then.Equals.Within: got %q, want %q", got, want)
	}
}

func TestCheckWhenEqualsThenExceedsWithin(t *testing.T) {
	r, err := CheckWhen("Ignition").Equals(IntRational(1)).Then("FuelPump").Exceeds(IntRational(0)).Within(50)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always(not(Ignition = 1) or eventually within 50ms (FuelPump > 0))"
	if got != want {
		t.Errorf("When.Equals.Then.Exceeds.Within: got %q, want %q", got, want)
	}
}

func TestCheckWhenThenStaysBetweenWithin(t *testing.T) {
	r, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("Speed").StaysBetween(IntRational(0), IntRational(10)).Within(200)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always(not(Brake > 50) or eventually within 200ms (0 <= Speed <= 10))"
	if got != want {
		t.Errorf("Then.StaysBetween.Within: got %q, want %q", got, want)
	}
}

// ===========================================================================
// Metadata
// ===========================================================================

func TestCheckMetadataNamedSeverity(t *testing.T) {
	r := CheckSignal("Speed").NeverExceeds(IntRational(220)).Named("SpeedLimit").Severity("critical")
	if r.Name() != "SpeedLimit" {
		t.Errorf("Name: got %q, want %q", r.Name(), "SpeedLimit")
	}
	if r.CheckSeverity() != "critical" {
		t.Errorf("Severity: got %q, want %q", r.CheckSeverity(), "critical")
	}
	if r.SignalName() != "Speed" {
		t.Errorf("SignalName: got %q, want %q", r.SignalName(), "Speed")
	}
	if got := mustDesc(t, r); got != "<= 220" {
		t.Errorf("ConditionDesc: got %q, want %q", got, "<= 220")
	}
}

func TestCheckSignalNameAndConditionDesc(t *testing.T) {
	r1 := CheckSignal("V").NeverBelow(Rational{Numerator: 23, Denominator: 2})
	if r1.SignalName() != "V" {
		t.Errorf("r1 SignalName: got %q", r1.SignalName())
	}
	if got := mustDesc(t, r1); got != ">= 11.5" {
		t.Errorf("r1 ConditionDesc: got %q", got)
	}

	r2 := CheckSignal("E").NeverEquals(IntRational(0))
	if r2.SignalName() != "E" {
		t.Errorf("r2 SignalName: got %q", r2.SignalName())
	}
	if got := mustDesc(t, r2); got != "!= 0" {
		t.Errorf("r2 ConditionDesc: got %q", got)
	}
}

func TestCheckWhenThenMetadata(t *testing.T) {
	r, err := CheckWhen("Brake").Exceeds(IntRational(50)).Then("Light").Equals(IntRational(1)).Within(100)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	if r.SignalName() != "Light" {
		t.Errorf("SignalName: got %q, want %q", r.SignalName(), "Light")
	}
	if got := mustDesc(t, r); got != "= 1 within 100ms" {
		t.Errorf("ConditionDesc: got %q, want %q", got, "= 1 within 100ms")
	}
}

// TestCheckConditionDescKernelCanonical pins that ConditionDesc renders
// thresholds through the kernel formatℚ, not Go's %g.  1e6 is the discriminator:
// %g renders it "1e+06" (scientific), the kernel renders the canonical
// "1000000" — so this both proves the delegation and matches the other bindings.
func TestCheckConditionDescKernelCanonical(t *testing.T) {
	r := CheckSignal("X").NeverExceeds(IntRational(1000000))
	if got := mustDesc(t, r); got != "<= 1000000" {
		t.Errorf("ConditionDesc: got %q, want %q (kernel-canonical, not %%g's 1e+06)", got, "<= 1000000")
	}
}

// ===========================================================================
// Error cases
// ===========================================================================

func TestCheckSettlesBetweenNegativeTime(t *testing.T) {
	_, err := CheckSignal("T").SettlesBetween(IntRational(0), IntRational(100)).Within(-1)
	if err == nil {
		t.Error("expected error for negative time")
	}
}

func TestCheckWhenThenNegativeTime(t *testing.T) {
	_, err := CheckWhen("A").Exceeds(IntRational(0)).Then("B").Equals(IntRational(1)).Within(-1)
	if err == nil {
		t.Error("expected error for negative time")
	}
}

// ===========================================================================
// Equivalence with manual construction
// ===========================================================================

func TestCheckNeverExceedsMatchesManual(t *testing.T) {
	checkF := CheckSignal("Speed").NeverExceeds(IntRational(220)).Formula()
	manualF := Always{Inner: Atomic{Predicate: LessThanOrEqual{Signal: "Speed", Value: IntRational(220)}}}
	if FormatFormula(checkF) != FormatFormula(manualF) {
		t.Errorf("mismatch: check=%q manual=%q",
			FormatFormula(checkF), FormatFormula(manualF))
	}
}

func TestCheckStaysBetweenMatchesManual(t *testing.T) {
	checkR, err := CheckSignal("V").StaysBetween(Rational{Numerator: 23, Denominator: 2}, Rational{Numerator: 29, Denominator: 2})
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	manualF := Always{Inner: Atomic{Predicate: Between{Signal: "V", Min: Rational{Numerator: 23, Denominator: 2}, Max: Rational{Numerator: 29, Denominator: 2}}}}
	if FormatFormula(checkR.Formula()) != FormatFormula(manualF) {
		t.Errorf("mismatch: check=%q manual=%q",
			FormatFormula(checkR.Formula()), FormatFormula(manualF))
	}
}

func TestCheckNeverEqualsMatchesManual(t *testing.T) {
	checkF := CheckSignal("Err").NeverEquals(IntRational(255)).Formula()
	manualF := Never(Equals{Signal: "Err", Value: IntRational(255)})
	if FormatFormula(checkF) != FormatFormula(manualF) {
		t.Errorf("mismatch: check=%q manual=%q",
			FormatFormula(checkF), FormatFormula(manualF))
	}
}

func TestCheckSettlesMatchesManual(t *testing.T) {
	checkR, err := CheckSignal("T").SettlesBetween(IntRational(60), IntRational(80)).Within(500)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	manualF := AlwaysWithin(
		TimeBound{Microseconds: 500_000},
		Atomic{Predicate: Between{Signal: "T", Min: IntRational(60), Max: IntRational(80)}},
	)
	if FormatFormula(checkR.Formula()) != FormatFormula(manualF) {
		t.Errorf("mismatch: check=%q manual=%q",
			FormatFormula(checkR.Formula()), FormatFormula(manualF))
	}
}

// ===========================================================================
// Client integration
// ===========================================================================

func TestAddChecks(t *testing.T) {
	mock := NewMockBackend(Respond(`{"status": "success"}`))
	client, err := NewClient(mock)
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	defer client.Close()

	staysBetween, err := CheckSignal("Voltage").StaysBetween(Rational{Numerator: 23, Denominator: 2}, Rational{Numerator: 29, Denominator: 2})
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	checks := []CheckResult{
		CheckSignal("Speed").NeverExceeds(IntRational(220)),
		staysBetween,
	}
	if err := client.AddChecks(ctx, checks); err != nil {
		t.Errorf("AddChecks: %v", err)
	}
}

func TestAddChecksWithDefaults(t *testing.T) {
	mock := NewMockBackend(Respond(`{"status": "success"}`))
	defaultCheck, err := CheckSignal("Voltage").StaysBetween(Rational{Numerator: 23, Denominator: 2}, Rational{Numerator: 29, Denominator: 2})
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	client, err := NewClient(mock, WithDefaultChecks(defaultCheck))
	if err != nil {
		t.Fatalf("NewClient: %v", err)
	}
	defer client.Close()

	// AddChecks should prepend the default check
	sessionChecks := []CheckResult{
		CheckSignal("Speed").NeverExceeds(IntRational(220)),
	}
	if err := client.AddChecks(ctx, sessionChecks); err != nil {
		t.Errorf("AddChecks with defaults: %v", err)
	}
}

func TestSerializeFormulaDepthLimit(t *testing.T) {
	// Build a formula nested 101 levels deep (exceeds maxFormulaDepth=100).
	var f Formula = Atomic{Predicate: Equals{Signal: "S", Value: IntRational(1)}}
	for i := 0; i < 101; i++ {
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
