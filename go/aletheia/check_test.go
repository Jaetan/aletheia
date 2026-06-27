// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"math"
	"testing"
)

// mustCheck panics if a check builder returned an error, else returns the
// CheckResult — for sites where the value is known-valid and only the formula
// is under test. Takes the builder's (CheckResult, error) pair directly so a
// builder call spreads into it: mustCheck(CheckSignal("S").NeverExceeds(1)).
func mustCheck(r CheckResult, err error) CheckResult {
	if err != nil {
		panic("unexpected check-builder error: " + err.Error())
	}
	return r
}

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
	r, err := CheckSignal("Speed").NeverExceeds(220)
	if err != nil {
		t.Fatalf("NeverExceeds: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always(Speed <= 220)"
	if got != want {
		t.Errorf("NeverExceeds: got %q, want %q", got, want)
	}
}

func TestCheckSignalNeverBelow(t *testing.T) {
	r, err := CheckSignal("Voltage").NeverBelow(11.5)
	if err != nil {
		t.Fatalf("NeverBelow: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always(Voltage >= 11.5)"
	if got != want {
		t.Errorf("NeverBelow: got %q, want %q", got, want)
	}
}

func TestCheckSignalStaysBetween(t *testing.T) {
	r, err := CheckSignal("Voltage").StaysBetween(11.5, 14.5)
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
	_, err := CheckSignal("Voltage").StaysBetween(14.5, 11.5)
	if err == nil {
		t.Fatal("expected error for inverted range")
	}
}

func TestCheckSignalSettlesBetweenInverted(t *testing.T) {
	_, err := CheckSignal("Temp").SettlesBetween(80, 60).Within(500)
	if err == nil {
		t.Fatal("expected error for inverted range")
	}
}

func TestCheckWhenThenStaysBetweenInverted(t *testing.T) {
	_, err := CheckWhen("Brake").Exceeds(50).Then("Speed").StaysBetween(10, 0).Within(200)
	if err == nil {
		t.Fatal("expected error for inverted range")
	}
}

func TestCheckSignalNeverEquals(t *testing.T) {
	r, err := CheckSignal("ErrorCode").NeverEquals(255)
	if err != nil {
		t.Fatalf("NeverEquals: %v", err)
	}
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
	r, err := CheckSignal("Gear").Equals(0).Always()
	if err != nil {
		t.Fatalf("Equals.Always: %v", err)
	}
	got := FormatFormula(r.Formula())
	want := "always(Gear = 0)"
	if got != want {
		t.Errorf("Equals.Always: got %q, want %q", got, want)
	}
}

func TestCheckSignalSettlesBetweenWithin(t *testing.T) {
	r, err := CheckSignal("Temp").SettlesBetween(60, 80).Within(500)
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
	r, err := CheckWhen("Brake").Exceeds(50).Then("BrakeLight").Equals(1).Within(100)
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
	r, err := CheckWhen("Voltage").DropsBelow(11).Then("Warning").Equals(1).Within(50)
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
	r, err := CheckWhen("Ignition").Equals(1).Then("FuelPump").Exceeds(0).Within(50)
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
	r, err := CheckWhen("Brake").Exceeds(50).Then("Speed").StaysBetween(0, 10).Within(200)
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
	r := mustCheck(CheckSignal("Speed").NeverExceeds(220)).Named("SpeedLimit").Severity("critical")
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
	r1 := mustCheck(CheckSignal("V").NeverBelow(11.5))
	if r1.SignalName() != "V" {
		t.Errorf("r1 SignalName: got %q", r1.SignalName())
	}
	if got := mustDesc(t, r1); got != ">= 11.5" {
		t.Errorf("r1 ConditionDesc: got %q", got)
	}

	r2 := mustCheck(CheckSignal("E").NeverEquals(0))
	if r2.SignalName() != "E" {
		t.Errorf("r2 SignalName: got %q", r2.SignalName())
	}
	if got := mustDesc(t, r2); got != "!= 0" {
		t.Errorf("r2 ConditionDesc: got %q", got)
	}
}

func TestCheckWhenThenMetadata(t *testing.T) {
	r, err := CheckWhen("Brake").Exceeds(50).Then("Light").Equals(1).Within(100)
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
	r := mustCheck(CheckSignal("X").NeverExceeds(1000000))
	if got := mustDesc(t, r); got != "<= 1000000" {
		t.Errorf("ConditionDesc: got %q, want %q (kernel-canonical, not %%g's 1e+06)", got, "<= 1000000")
	}
}

// ===========================================================================
// Error cases
// ===========================================================================

func TestCheckSettlesBetweenNegativeTime(t *testing.T) {
	_, err := CheckSignal("T").SettlesBetween(0, 100).Within(-1)
	if err == nil {
		t.Error("expected error for negative time")
	}
}

func TestCheckWhenThenNegativeTime(t *testing.T) {
	_, err := CheckWhen("A").Exceeds(0).Then("B").Equals(1).Within(-1)
	if err == nil {
		t.Error("expected error for negative time")
	}
}

// TestCheckBuilderRejectsNonFiniteValue locks in the cross-binding contract:
// a NaN / Inf value must FAIL (matching the Python and C++ bindings), never
// silently clamp to 0/1 as the old physicalAsRational path did. Covers every
// builder shape — terminal, two-step, range, settles, and the when/then chain.
func TestCheckBuilderRejectsNonFiniteValue(t *testing.T) {
	nan := PhysicalValue(math.NaN())
	inf := PhysicalValue(math.Inf(1))

	if _, err := CheckSignal("S").NeverExceeds(nan); err == nil {
		t.Error("NeverExceeds(NaN): expected error, got nil")
	}
	if _, err := CheckSignal("S").NeverBelow(inf); err == nil {
		t.Error("NeverBelow(Inf): expected error, got nil")
	}
	if _, err := CheckSignal("S").NeverEquals(nan); err == nil {
		t.Error("NeverEquals(NaN): expected error, got nil")
	}
	if _, err := CheckSignal("S").Equals(nan).Always(); err == nil {
		t.Error("Equals(NaN).Always: expected error, got nil")
	}
	if _, err := CheckSignal("S").StaysBetween(nan, 10); err == nil {
		t.Error("StaysBetween(NaN, _): expected error, got nil")
	}
	if _, err := CheckSignal("S").SettlesBetween(0, inf).Within(100); err == nil {
		t.Error("SettlesBetween(_, Inf).Within: expected error, got nil")
	}
	if _, err := CheckWhen("A").Exceeds(nan).Then("B").Equals(1).Within(100); err == nil {
		t.Error("when Exceeds(NaN): expected error, got nil")
	}
	if _, err := CheckWhen("A").Exceeds(1).Then("B").Equals(inf).Within(100); err == nil {
		t.Error("then Equals(Inf): expected error, got nil")
	}
}

// ===========================================================================
// Equivalence with manual construction
// ===========================================================================

func TestCheckNeverExceedsMatchesManual(t *testing.T) {
	checkF := mustCheck(CheckSignal("Speed").NeverExceeds(220)).Formula()
	manualF := Always{Inner: Atomic{Predicate: LessThanOrEqual{Signal: "Speed", Value: RationalFromFloat(220)}}}
	if FormatFormula(checkF) != FormatFormula(manualF) {
		t.Errorf("mismatch: check=%q manual=%q",
			FormatFormula(checkF), FormatFormula(manualF))
	}
}

func TestCheckStaysBetweenMatchesManual(t *testing.T) {
	checkR, err := CheckSignal("V").StaysBetween(11.5, 14.5)
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	manualF := Always{Inner: Atomic{Predicate: Between{Signal: "V", Min: RationalFromFloat(11.5), Max: RationalFromFloat(14.5)}}}
	if FormatFormula(checkR.Formula()) != FormatFormula(manualF) {
		t.Errorf("mismatch: check=%q manual=%q",
			FormatFormula(checkR.Formula()), FormatFormula(manualF))
	}
}

func TestCheckNeverEqualsMatchesManual(t *testing.T) {
	checkF := mustCheck(CheckSignal("Err").NeverEquals(255)).Formula()
	manualF := Never(Equals{Signal: "Err", Value: RationalFromFloat(255)})
	if FormatFormula(checkF) != FormatFormula(manualF) {
		t.Errorf("mismatch: check=%q manual=%q",
			FormatFormula(checkF), FormatFormula(manualF))
	}
}

func TestCheckSettlesMatchesManual(t *testing.T) {
	checkR, err := CheckSignal("T").SettlesBetween(60, 80).Within(500)
	if err != nil {
		t.Fatalf("Within: %v", err)
	}
	manualF := AlwaysWithin(
		TimeBound{Microseconds: 500_000},
		Atomic{Predicate: Between{Signal: "T", Min: RationalFromFloat(60), Max: RationalFromFloat(80)}},
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

	staysBetween, err := CheckSignal("Voltage").StaysBetween(11.5, 14.5)
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	checks := []CheckResult{
		mustCheck(CheckSignal("Speed").NeverExceeds(220)),
		staysBetween,
	}
	if err := client.AddChecks(ctx, checks); err != nil {
		t.Errorf("AddChecks: %v", err)
	}
}

func TestAddChecksWithDefaults(t *testing.T) {
	mock := NewMockBackend(Respond(`{"status": "success"}`))
	defaultCheck, err := CheckSignal("Voltage").StaysBetween(11.5, 14.5)
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
		mustCheck(CheckSignal("Speed").NeverExceeds(220)),
	}
	if err := client.AddChecks(ctx, sessionChecks); err != nil {
		t.Errorf("AddChecks with defaults: %v", err)
	}
}

func TestSerializeFormulaDepthLimit(t *testing.T) {
	// Build a formula nested 101 levels deep (exceeds maxFormulaDepth=100).
	var f Formula = Atomic{Predicate: Equals{Signal: "S", Value: RationalFromFloat(1)}}
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
