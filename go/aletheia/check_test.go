package aletheia

import (
	"encoding/json"
	"errors"
	"testing"
)

// ===========================================================================
// One-shot methods
// ===========================================================================

func TestCheckSignalNeverExceeds(t *testing.T) {
	r := CheckSignal("Speed").NeverExceeds(220)
	got := FormatFormula(r.Formula())
	want := "always(Speed < 220)"
	if got != want {
		t.Errorf("NeverExceeds: got %q, want %q", got, want)
	}
}

func TestCheckSignalNeverBelow(t *testing.T) {
	r := CheckSignal("Voltage").NeverBelow(11.5)
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
	r := CheckSignal("ErrorCode").NeverEquals(255)
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
	r := CheckSignal("Gear").Equals(0).Always()
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
	r := CheckSignal("Speed").NeverExceeds(220).Named("SpeedLimit").Severity("critical")
	if r.Name() != "SpeedLimit" {
		t.Errorf("Name: got %q, want %q", r.Name(), "SpeedLimit")
	}
	if r.CheckSeverity() != "critical" {
		t.Errorf("Severity: got %q, want %q", r.CheckSeverity(), "critical")
	}
	if r.SignalName() != "Speed" {
		t.Errorf("SignalName: got %q, want %q", r.SignalName(), "Speed")
	}
	if r.ConditionDesc() != "< 220" {
		t.Errorf("ConditionDesc: got %q, want %q", r.ConditionDesc(), "< 220")
	}
}

func TestCheckSignalNameAndConditionDesc(t *testing.T) {
	r1 := CheckSignal("V").NeverBelow(11.5)
	if r1.SignalName() != "V" {
		t.Errorf("r1 SignalName: got %q", r1.SignalName())
	}
	if r1.ConditionDesc() != ">= 11.5" {
		t.Errorf("r1 ConditionDesc: got %q", r1.ConditionDesc())
	}

	r2 := CheckSignal("E").NeverEquals(0)
	if r2.SignalName() != "E" {
		t.Errorf("r2 SignalName: got %q", r2.SignalName())
	}
	if r2.ConditionDesc() != "!= 0" {
		t.Errorf("r2 ConditionDesc: got %q", r2.ConditionDesc())
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
	if r.ConditionDesc() != "= 1 within 100ms" {
		t.Errorf("ConditionDesc: got %q, want %q", r.ConditionDesc(), "= 1 within 100ms")
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

// ===========================================================================
// Equivalence with manual construction
// ===========================================================================

func TestCheckNeverExceedsMatchesManual(t *testing.T) {
	checkF := CheckSignal("Speed").NeverExceeds(220).Formula()
	manualF := Always{Inner: Atomic{Predicate: LessThan{Signal: "Speed", Value: 220}}}
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
	manualF := Always{Inner: Atomic{Predicate: Between{Signal: "V", Min: 11.5, Max: 14.5}}}
	if FormatFormula(checkR.Formula()) != FormatFormula(manualF) {
		t.Errorf("mismatch: check=%q manual=%q",
			FormatFormula(checkR.Formula()), FormatFormula(manualF))
	}
}

func TestCheckNeverEqualsMatchesManual(t *testing.T) {
	checkF := CheckSignal("Err").NeverEquals(255).Formula()
	manualF := Never(Equals{Signal: "Err", Value: 255})
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
		Atomic{Predicate: Between{Signal: "T", Min: 60, Max: 80}},
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
		CheckSignal("Speed").NeverExceeds(220),
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
		CheckSignal("Speed").NeverExceeds(220),
	}
	if err := client.AddChecks(ctx, sessionChecks); err != nil {
		t.Errorf("AddChecks with defaults: %v", err)
	}
}

func TestSerializeDataFrame(t *testing.T) {
	sid, err := NewStandardID(0x100)
	if err != nil {
		t.Fatal(err)
	}
	dlc, err := NewDLC(4)
	if err != nil {
		t.Fatal(err)
	}
	ts := Timestamp{Microseconds: 1000}
	data := FramePayload{0x01, 0x02, 0x03, 0x04}

	result := serializeDataFrame(ts, sid, dlc, data)

	// Parse the output as JSON and verify fields.
	var m map[string]any
	if err := json.Unmarshal([]byte(result), &m); err != nil {
		t.Fatalf("invalid JSON: %v", err)
	}
	if m["type"] != "data" {
		t.Errorf("type = %v, want %q", m["type"], "data")
	}
	if m["timestamp"] != float64(1000) {
		t.Errorf("timestamp = %v, want 1000", m["timestamp"])
	}
	if m["id"] != float64(0x100) {
		t.Errorf("id = %v, want %d", m["id"], 0x100)
	}
	if m["extended"] != false {
		t.Errorf("extended = %v, want false", m["extended"])
	}
	if m["dlc"] != float64(4) {
		t.Errorf("dlc = %v, want 4", m["dlc"])
	}
	dataArr, ok := m["data"].([]any)
	if !ok {
		t.Fatalf("data is not an array: %T", m["data"])
	}
	if len(dataArr) != 4 {
		t.Fatalf("data length = %d, want 4", len(dataArr))
	}
	for i, want := range []float64{1, 2, 3, 4} {
		if dataArr[i] != want {
			t.Errorf("data[%d] = %v, want %v", i, dataArr[i], want)
		}
	}
}

func TestSerializeDataFrameExtended(t *testing.T) {
	eid, err := NewExtendedID(0x18FEF100)
	if err != nil {
		t.Fatal(err)
	}
	dlc, err := NewDLC(8)
	if err != nil {
		t.Fatal(err)
	}
	ts := Timestamp{Microseconds: 500}
	data := FramePayload{0xFF, 0x00, 0xAA, 0x55, 0x01, 0x02, 0x03, 0x04}

	result := serializeDataFrame(ts, eid, dlc, data)

	var m map[string]any
	if err := json.Unmarshal([]byte(result), &m); err != nil {
		t.Fatalf("invalid JSON: %v", err)
	}
	if m["extended"] != true {
		t.Errorf("extended = %v, want true", m["extended"])
	}
	if m["id"] != float64(0x18FEF100) {
		t.Errorf("id = %v, want %d", m["id"], 0x18FEF100)
	}
}

func TestSerializeFormulaDepthLimit(t *testing.T) {
	// Build a formula nested 101 levels deep (exceeds maxFormulaDepth=100).
	var f Formula = Atomic{Predicate: Equals{Signal: "S", Value: 1}}
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
