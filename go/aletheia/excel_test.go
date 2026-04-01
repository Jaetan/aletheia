package aletheia

import (
	"math"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/xuri/excelize/v2"
)

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

func makeChecksWorkbook(t *testing.T, rows [][]interface{}) string {
	t.Helper()
	f := excelize.NewFile()
	defer f.Close()
	if err := f.SetSheetName("Sheet1", "Checks"); err != nil {
		t.Fatal(err)
	}
	for i, h := range checksHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("Checks", cell, h)
	}
	for rowIdx, row := range rows {
		for colIdx, val := range row {
			if val == nil {
				continue
			}
			cell, _ := excelize.CoordinatesToCellName(colIdx+1, rowIdx+2)
			_ = f.SetCellValue("Checks", cell, val)
		}
	}
	path := filepath.Join(t.TempDir(), "test.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	return path
}

func makeWhenThenWorkbook(t *testing.T, rows [][]interface{}) string {
	t.Helper()
	f := excelize.NewFile()
	defer f.Close()
	if err := f.SetSheetName("Sheet1", "When-Then"); err != nil {
		t.Fatal(err)
	}
	for i, h := range whenThenHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("When-Then", cell, h)
	}
	for rowIdx, row := range rows {
		for colIdx, val := range row {
			if val == nil {
				continue
			}
			cell, _ := excelize.CoordinatesToCellName(colIdx+1, rowIdx+2)
			_ = f.SetCellValue("When-Then", cell, val)
		}
	}
	path := filepath.Join(t.TempDir(), "test.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	return path
}

func makeDbcWorkbook(t *testing.T, rows [][]interface{}) string {
	t.Helper()
	f := excelize.NewFile()
	defer f.Close()
	if err := f.SetSheetName("Sheet1", "DBC"); err != nil {
		t.Fatal(err)
	}
	for i, h := range dbcHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("DBC", cell, h)
	}
	for rowIdx, row := range rows {
		for colIdx, val := range row {
			if val == nil {
				continue
			}
			cell, _ := excelize.CoordinatesToCellName(colIdx+1, rowIdx+2)
			_ = f.SetCellValue("DBC", cell, val)
		}
	}
	path := filepath.Join(t.TempDir(), "test.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	return path
}

// ===========================================================================
// Simple checks -- each condition type
// ===========================================================================

func TestLoadExcelNeverExceeds(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil},
	})
	checks, err := LoadChecksFromExcel(path)
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

func TestLoadExcelNeverBelow(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Voltage", "never_below", 11.5, nil, nil, nil, nil},
	})
	checks, err := LoadChecksFromExcel(path)
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

func TestLoadExcelStaysBetween(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Voltage", "stays_between", nil, 11.5, 14.5, nil, nil},
	})
	checks, err := LoadChecksFromExcel(path)
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

func TestLoadExcelNeverEquals(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "ErrorCode", "never_equals", 255, nil, nil, nil, nil},
	})
	checks, err := LoadChecksFromExcel(path)
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

func TestLoadExcelEqualsAlways(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Gear", "equals", 0, nil, nil, nil, nil},
	})
	checks, err := LoadChecksFromExcel(path)
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

func TestLoadExcelSettlesBetween(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "CoolantTemp", "settles_between", nil, 80, 100, 5000, nil},
	})
	checks, err := LoadChecksFromExcel(path)
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

func TestLoadExcelMultipleChecks(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil},
		{nil, "Voltage", "stays_between", nil, 11.5, 14.5, nil, nil},
	})
	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 2 {
		t.Fatalf("expected 2 checks, got %d", len(checks))
	}
}

// ===========================================================================
// When/Then checks
// ===========================================================================

func TestLoadExcelWhenExceedsThenEquals(t *testing.T) {
	// name, when_sig, when_cond, when_val, then_sig, then_cond, then_val, then_min, then_max, within, sev
	path := makeWhenThenWorkbook(t, [][]interface{}{
		{"Brake response", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, nil, nil, 100, nil},
	})
	checks, err := LoadChecksFromExcel(path)
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

func TestLoadExcelWhenEqualsThenExceeds(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]interface{}{
		{nil, "Ignition", "equals", 1, "RPM", "exceeds", 500, nil, nil, 2000, nil},
	})
	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	expected, _ := CheckWhen("Ignition").Equals(1).Then("RPM").Exceeds(500).Within(2000)
	want := FormatFormula(expected.Formula())
	got := FormatFormula(checks[0].Formula())
	if got != want {
		t.Errorf("formula mismatch: got %q, want %q", got, want)
	}
}

func TestLoadExcelWhenDropsBelowThenStaysBetween(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]interface{}{
		{nil, "FuelLevel", "drops_below", 10, "FuelWarning", "stays_between", nil, 1, 1, 50, nil},
	})
	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
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

func TestLoadExcelNameSet(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{"Speed limit", "Speed", "never_exceeds", 220, nil, nil, nil, nil},
	})
	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].Name() != "Speed limit" {
		t.Errorf("Name: got %q, want %q", checks[0].Name(), "Speed limit")
	}
}

func TestLoadExcelSeveritySet(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Speed", "never_exceeds", 220, nil, nil, nil, "critical"},
	})
	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].CheckSeverity() != "critical" {
		t.Errorf("Severity: got %q, want %q", checks[0].CheckSeverity(), "critical")
	}
}

func TestLoadExcelNameAndSeverity(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{"Speed limit", "Speed", "never_exceeds", 220, nil, nil, nil, "warning"},
	})
	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].Name() != "Speed limit" {
		t.Errorf("Name: got %q", checks[0].Name())
	}
	if checks[0].CheckSeverity() != "warning" {
		t.Errorf("Severity: got %q", checks[0].CheckSeverity())
	}
}

func TestLoadExcelDefaultsEmpty(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil},
	})
	checks, err := LoadChecksFromExcel(path)
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

func TestLoadExcelWhenThenMetadata(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]interface{}{
		{"Brake response", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, nil, nil, 100, "safety"},
	})
	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].Name() != "Brake response" {
		t.Errorf("Name: got %q", checks[0].Name())
	}
	if checks[0].CheckSeverity() != "safety" {
		t.Errorf("Severity: got %q", checks[0].CheckSeverity())
	}
}

// ===========================================================================
// DBC parsing
// ===========================================================================

func TestLoadExcelDbcSingleSignal(t *testing.T) {
	// id, name, extended, dlc, signal, startbit, length, byteorder, signed, factor, offset, min, max, unit
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, "rpm"},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if dbc.Version != "" {
		t.Errorf("Version: got %q", dbc.Version)
	}
	if len(dbc.Messages) != 1 {
		t.Fatalf("expected 1 message, got %d", len(dbc.Messages))
	}
	msg := dbc.Messages[0]
	if string(msg.Name) != "EngineData" {
		t.Errorf("Name: got %q", msg.Name)
	}
	if msg.DLC.Value() != 8 {
		t.Errorf("DLC: got %d", msg.DLC.Value())
	}
	if len(msg.Signals) != 1 {
		t.Fatalf("expected 1 signal, got %d", len(msg.Signals))
	}
	sig := msg.Signals[0]
	if string(sig.Name) != "RPM" {
		t.Errorf("Signal name: got %q", sig.Name)
	}
	if sig.StartBit != 0 {
		t.Errorf("StartBit: got %d", sig.StartBit)
	}
	if sig.BitLength != 16 {
		t.Errorf("BitLength: got %d", sig.BitLength)
	}
	if sig.ByteOrder != LittleEndian {
		t.Errorf("ByteOrder: got %d", sig.ByteOrder)
	}
	if sig.IsSigned {
		t.Error("IsSigned: expected false")
	}
	if sig.Factor.Float64() != 0.25 {
		t.Errorf("Factor: got %f", sig.Factor.Float64())
	}
	if sig.Offset.Numerator != 0 {
		t.Errorf("Offset: got %d/%d", sig.Offset.Numerator, sig.Offset.Denominator)
	}
	if string(sig.Unit) != "rpm" {
		t.Errorf("Unit: got %q", sig.Unit)
	}
	if _, ok := sig.Presence.(AlwaysPresent); !ok {
		t.Errorf("Presence: expected AlwaysPresent, got %T", sig.Presence)
	}
}

func TestLoadExcelDbcMessageGrouping(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, "rpm"},
		{256, "EngineData", "FALSE", 8, "Temp", 16, 8, "little_endian", "FALSE", 1, -40, -40, 215, "C"},
		{512, "BrakeData", "FALSE", 4, "BrakePressure", 0, 16, "big_endian", "FALSE", 0.1, 0, 0, 6553.5, "bar"},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(dbc.Messages) != 2 {
		t.Fatalf("expected 2 messages, got %d", len(dbc.Messages))
	}
	if string(dbc.Messages[0].Name) != "EngineData" {
		t.Errorf("msg[0] name: got %q", dbc.Messages[0].Name)
	}
	if len(dbc.Messages[0].Signals) != 2 {
		t.Fatalf("msg[0] signals: expected 2, got %d", len(dbc.Messages[0].Signals))
	}
	if string(dbc.Messages[0].Signals[0].Name) != "RPM" {
		t.Errorf("msg[0].sig[0]: got %q", dbc.Messages[0].Signals[0].Name)
	}
	if string(dbc.Messages[0].Signals[1].Name) != "Temp" {
		t.Errorf("msg[0].sig[1]: got %q", dbc.Messages[0].Signals[1].Name)
	}
	if string(dbc.Messages[1].Name) != "BrakeData" {
		t.Errorf("msg[1] name: got %q", dbc.Messages[1].Name)
	}
	if len(dbc.Messages[1].Signals) != 1 {
		t.Fatalf("msg[1] signals: expected 1, got %d", len(dbc.Messages[1].Signals))
	}
}

func TestLoadExcelDbcHexID(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{"0x100", "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, "rpm"},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if dbc.Messages[0].ID.Value() != 0x100 {
		t.Errorf("ID: got %d, want %d", dbc.Messages[0].ID.Value(), 0x100)
	}
}

func TestLoadExcelDbcSignedTrue(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "EngineData", "FALSE", 8, "Temp", 0, 8, "little_endian", "TRUE", 1, -40, -40, 215, "C"},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !dbc.Messages[0].Signals[0].IsSigned {
		t.Error("expected IsSigned=true")
	}
}

func TestLoadExcelDbcSignedIntegerOne(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "Msg", "FALSE", 8, "Sig", 0, 8, "little_endian", 1, 1, 0, 0, 255, ""},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !dbc.Messages[0].Signals[0].IsSigned {
		t.Error("expected IsSigned=true for integer 1")
	}
}

func TestLoadExcelDbcSignedIntegerZero(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "Msg", "FALSE", 8, "Sig", 0, 8, "little_endian", 0, 1, 0, 0, 255, ""},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if dbc.Messages[0].Signals[0].IsSigned {
		t.Error("expected IsSigned=false for integer 0")
	}
}

func TestLoadExcelDbcMissingUnit(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, nil},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if string(dbc.Messages[0].Signals[0].Unit) != "" {
		t.Errorf("Unit: got %q, want empty", dbc.Messages[0].Signals[0].Unit)
	}
}

// ===========================================================================
// Multiplexed signals
// ===========================================================================

func TestLoadExcelDbcAlwaysPresent(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", nil, nil},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	sig := dbc.Messages[0].Signals[0]
	if _, ok := sig.Presence.(AlwaysPresent); !ok {
		t.Errorf("expected AlwaysPresent, got %T", sig.Presence)
	}
}

func TestLoadExcelDbcMultiplexed(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "Msg", "FALSE", 8, "MuxSignal", 8, 8, "little_endian", "FALSE", 1, 0, 0, 255, "", "Selector", 3},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	sig := dbc.Messages[0].Signals[0]
	mux, ok := sig.Presence.(Multiplexed)
	if !ok {
		t.Fatalf("expected Multiplexed, got %T", sig.Presence)
	}
	if string(mux.Multiplexor) != "Selector" {
		t.Errorf("Multiplexor: got %q", mux.Multiplexor)
	}
	if mux.MuxValue != 3 {
		t.Errorf("MuxValue: got %d", mux.MuxValue)
	}
}

func TestLoadExcelDbcMixedPresence(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "Msg", "FALSE", 8, "Selector", 0, 8, "little_endian", "FALSE", 1, 0, 0, 255, "", nil, nil},
		{256, "Msg", "FALSE", 8, "TempA", 8, 8, "little_endian", "FALSE", 1, -40, -40, 215, "C", "Selector", 0},
		{256, "Msg", "FALSE", 8, "TempB", 8, 8, "little_endian", "FALSE", 1, -40, -40, 215, "C", "Selector", 1},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	msg := dbc.Messages[0]
	if len(msg.Signals) != 3 {
		t.Fatalf("expected 3 signals, got %d", len(msg.Signals))
	}
	if _, ok := msg.Signals[0].Presence.(AlwaysPresent); !ok {
		t.Errorf("sig[0] expected AlwaysPresent, got %T", msg.Signals[0].Presence)
	}
	if mux, ok := msg.Signals[1].Presence.(Multiplexed); !ok || string(mux.Multiplexor) != "Selector" || mux.MuxValue != 0 {
		t.Errorf("sig[1] expected Multiplexed(Selector, 0), got %v", msg.Signals[1].Presence)
	}
	if mux, ok := msg.Signals[2].Presence.(Multiplexed); !ok || string(mux.Multiplexor) != "Selector" || mux.MuxValue != 1 {
		t.Errorf("sig[2] expected Multiplexed(Selector, 1), got %v", msg.Signals[2].Presence)
	}
}

func TestLoadExcelDbcPartialMuxError(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", "Selector", nil},
	})
	_, err := LoadDbcFromExcel(path)
	if err == nil {
		t.Fatal("expected error for partial mux")
	}
	if !strings.Contains(err.Error(), "must both be provided or both be empty") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelDbcPartialMuxValueOnlyError(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", nil, 3},
	})
	_, err := LoadDbcFromExcel(path)
	if err == nil {
		t.Fatal("expected error for partial mux value only")
	}
	if !strings.Contains(err.Error(), "must both be provided or both be empty") {
		t.Errorf("unexpected error: %v", err)
	}
}

// ===========================================================================
// Template creation
// ===========================================================================

func TestCreateExcelTemplateCreatesFile(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateExcelTemplate(path); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if _, err := os.Stat(path); os.IsNotExist(err) {
		t.Fatal("template file not created")
	}
}

func TestCreateExcelTemplateSheetNames(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateExcelTemplate(path); err != nil {
		t.Fatal(err)
	}
	f, err := excelize.OpenFile(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	sheets := f.GetSheetList()
	if len(sheets) != 3 {
		t.Fatalf("expected 3 sheets, got %d: %v", len(sheets), sheets)
	}
	if sheets[0] != "DBC" || sheets[1] != "Checks" || sheets[2] != "When-Then" {
		t.Errorf("unexpected sheet names: %v", sheets)
	}
}

func TestCreateExcelTemplateDbcHeaders(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateExcelTemplate(path); err != nil {
		t.Fatal(err)
	}
	f, err := excelize.OpenFile(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	rows, _ := f.GetRows("DBC")
	if len(rows) < 1 {
		t.Fatal("DBC sheet has no rows")
	}
	for i, want := range dbcHeaders {
		if i >= len(rows[0]) || rows[0][i] != want {
			got := ""
			if i < len(rows[0]) {
				got = rows[0][i]
			}
			t.Errorf("DBC header[%d]: got %q, want %q", i, got, want)
		}
	}
}

func TestCreateExcelTemplateChecksHeaders(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateExcelTemplate(path); err != nil {
		t.Fatal(err)
	}
	f, err := excelize.OpenFile(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	rows, _ := f.GetRows("Checks")
	if len(rows) < 1 {
		t.Fatal("Checks sheet has no rows")
	}
	for i, want := range checksHeaders {
		if i >= len(rows[0]) || rows[0][i] != want {
			got := ""
			if i < len(rows[0]) {
				got = rows[0][i]
			}
			t.Errorf("Checks header[%d]: got %q, want %q", i, got, want)
		}
	}
}

func TestCreateExcelTemplateWhenThenHeaders(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateExcelTemplate(path); err != nil {
		t.Fatal(err)
	}
	f, err := excelize.OpenFile(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	rows, _ := f.GetRows("When-Then")
	if len(rows) < 1 {
		t.Fatal("When-Then sheet has no rows")
	}
	for i, want := range whenThenHeaders {
		if i >= len(rows[0]) || rows[0][i] != want {
			got := ""
			if i < len(rows[0]) {
				got = rows[0][i]
			}
			t.Errorf("When-Then header[%d]: got %q, want %q", i, got, want)
		}
	}
}

func TestCreateExcelTemplateHeadersBold(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateExcelTemplate(path); err != nil {
		t.Fatal(err)
	}
	f, err := excelize.OpenFile(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	for _, sheet := range []string{"DBC", "Checks", "When-Then"} {
		rows, _ := f.GetRows(sheet)
		if len(rows) < 1 {
			t.Fatalf("%s: no header row", sheet)
		}
		for col := range rows[0] {
			cell, _ := excelize.CoordinatesToCellName(col+1, 1)
			styleID, err := f.GetCellStyle(sheet, cell)
			if err != nil {
				t.Fatalf("GetCellStyle(%s, %s): %v", sheet, cell, err)
			}
			if styleID == 0 {
				// Style 0 is the default (no formatting). Bold headers should have a non-zero style.
				t.Errorf("%s header cell %s has default style (not bold)", sheet, cell)
			}
		}
	}
}

func TestCreateExcelTemplateNoOverwrite(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateExcelTemplate(path); err != nil {
		t.Fatal(err)
	}
	err := CreateExcelTemplate(path)
	if err == nil {
		t.Fatal("expected error when file exists")
	}
	if !strings.Contains(err.Error(), "file already exists") {
		t.Errorf("unexpected error: %v", err)
	}
}

// ===========================================================================
// Error handling
// ===========================================================================

func TestLoadExcelFileNotFound(t *testing.T) {
	_, err := LoadChecksFromExcel("/nonexistent/path/checks.xlsx")
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "Excel file not found") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelDbcFileNotFound(t *testing.T) {
	_, err := LoadDbcFromExcel("/nonexistent/path/dbc.xlsx")
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "Excel file not found") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelNoChecksOrWhenThenSheet(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	_ = f.SetSheetName("Sheet1", "Other")
	dir := t.TempDir()
	path := filepath.Join(dir, "bad.xlsx")
	_ = f.SaveAs(path)

	_, err := LoadChecksFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "no 'Checks' or 'When-Then' sheet") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelNoDbcSheet(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	_ = f.SetSheetName("Sheet1", "Other")
	dir := t.TempDir()
	path := filepath.Join(dir, "bad.xlsx")
	_ = f.SaveAs(path)

	_, err := LoadDbcFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "no 'DBC' sheet") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelUnknownSimpleCondition(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Speed", "bogus", 100, nil, nil, nil, nil},
	})
	_, err := LoadChecksFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "unknown condition 'bogus'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelMissingValueForNeverExceeds(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Speed", "never_exceeds", nil, nil, nil, nil, nil},
	})
	_, err := LoadChecksFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "missing or invalid 'Value'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelStaysBetweenMissingMin(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Voltage", "stays_between", nil, nil, 14.5, nil, nil},
	})
	_, err := LoadChecksFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "requires 'Min' and 'Max'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelSettlesBetweenMissingTime(t *testing.T) {
	path := makeChecksWorkbook(t, [][]interface{}{
		{nil, "Temp", "settles_between", nil, 80, 100, nil, nil},
	})
	_, err := LoadChecksFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "requires 'Time (ms)'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelUnknownWhenCondition(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]interface{}{
		{nil, "Brake", "bogus", 50, "BrakeLight", "equals", 1, nil, nil, 100, nil},
	})
	_, err := LoadChecksFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "unknown when condition 'bogus'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelUnknownThenCondition(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]interface{}{
		{nil, "Brake", "exceeds", 50, "BrakeLight", "bogus", 1, nil, nil, 100, nil},
	})
	_, err := LoadChecksFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "unknown then condition 'bogus'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelInvalidByteOrder(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "Msg", "FALSE", 8, "Sig", 0, 16, "mixed_endian", "FALSE", 1, 0, 0, 100, ""},
	})
	_, err := LoadDbcFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "Byte Order") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelInvalidMessageID(t *testing.T) {
	path := makeDbcWorkbook(t, [][]interface{}{
		{"not_a_number", "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, ""},
	})
	_, err := LoadDbcFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	if !strings.Contains(err.Error(), "invalid 'Message ID'") {
		t.Errorf("unexpected error: %v", err)
	}
}

func TestLoadExcelDbcEmptyData(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	_ = f.SetSheetName("Sheet1", "DBC")
	for i, h := range dbcHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("DBC", cell, h)
	}
	dir := t.TempDir()
	path := filepath.Join(dir, "empty.xlsx")
	_ = f.SaveAs(path)

	_, err := LoadDbcFromExcel(path)
	if err == nil {
		t.Fatal("expected error")
	}
	// The error could be "at least one data row" or "no data rows" depending
	// on how excelize reports the sheet rows.
	msg := err.Error()
	if !strings.Contains(msg, "data row") {
		t.Errorf("unexpected error: %v", err)
	}
}

// ===========================================================================
// Empty row skip
// ===========================================================================

func TestLoadExcelEmptyRowSkipped(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	_ = f.SetSheetName("Sheet1", "Checks")
	for i, h := range checksHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("Checks", cell, h)
	}
	// Row 2: Speed never_exceeds 220
	_ = f.SetCellValue("Checks", "B2", "Speed")
	_ = f.SetCellValue("Checks", "C2", "never_exceeds")
	_ = f.SetCellValue("Checks", "D2", 220)
	// Row 3: empty (skipped)
	// Row 4: Voltage never_below 11.5
	_ = f.SetCellValue("Checks", "B4", "Voltage")
	_ = f.SetCellValue("Checks", "C4", "never_below")
	_ = f.SetCellValue("Checks", "D4", 11.5)

	dir := t.TempDir()
	path := filepath.Join(dir, "gaps.xlsx")
	_ = f.SaveAs(path)

	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 2 {
		t.Fatalf("expected 2 checks (empty row skipped), got %d", len(checks))
	}
}

// ===========================================================================
// Combined Checks + When-Then
// ===========================================================================

func TestLoadExcelCombinedSheets(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()

	// Checks sheet
	_ = f.SetSheetName("Sheet1", "Checks")
	for i, h := range checksHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("Checks", cell, h)
	}
	_ = f.SetCellValue("Checks", "B2", "Speed")
	_ = f.SetCellValue("Checks", "C2", "never_exceeds")
	_ = f.SetCellValue("Checks", "D2", 220)

	// When-Then sheet
	_, _ = f.NewSheet("When-Then")
	for i, h := range whenThenHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("When-Then", cell, h)
	}
	_ = f.SetCellValue("When-Then", "B2", "Brake")
	_ = f.SetCellValue("When-Then", "C2", "exceeds")
	_ = f.SetCellValue("When-Then", "D2", 50)
	_ = f.SetCellValue("When-Then", "E2", "BrakeLight")
	_ = f.SetCellValue("When-Then", "F2", "equals")
	_ = f.SetCellValue("When-Then", "G2", 1)
	_ = f.SetCellValue("When-Then", "J2", 100)

	dir := t.TempDir()
	path := filepath.Join(dir, "combined.xlsx")
	_ = f.SaveAs(path)

	checks, err := LoadChecksFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 2 {
		t.Fatalf("expected 2 checks, got %d", len(checks))
	}
	// First is simple check, second is when/then.
	want0 := FormatFormula(CheckSignal("Speed").NeverExceeds(220).Formula())
	got0 := FormatFormula(checks[0].Formula())
	if got0 != want0 {
		t.Errorf("check[0] formula mismatch: got %q, want %q", got0, want0)
	}
	expected1, _ := CheckWhen("Brake").Exceeds(50).Then("BrakeLight").Equals(1).Within(100)
	want1 := FormatFormula(expected1.Formula())
	got1 := FormatFormula(checks[1].Formula())
	if got1 != want1 {
		t.Errorf("check[1] formula mismatch: got %q, want %q", got1, want1)
	}
}

// ===========================================================================
// Rational conversion
// ===========================================================================

func TestDoubleToRationalInteger(t *testing.T) {
	r, err := doubleToRational(42.0)
	if err != nil {
		t.Fatal(err)
	}
	if r.Numerator != 42 || r.Denominator != 1 {
		t.Errorf("expected 42/1, got %d/%d", r.Numerator, r.Denominator)
	}
}

func TestDoubleToRationalFraction(t *testing.T) {
	r, err := doubleToRational(0.25)
	if err != nil {
		t.Fatal(err)
	}
	if r.Float64() != 0.25 {
		t.Errorf("expected 0.25, got %f", r.Float64())
	}
	// 0.25 = 250000/1000000 = 1/4
	if r.Numerator != 1 || r.Denominator != 4 {
		t.Errorf("expected 1/4, got %d/%d", r.Numerator, r.Denominator)
	}
}

func TestDoubleToRationalNegative(t *testing.T) {
	r, err := doubleToRational(-40.0)
	if err != nil {
		t.Fatal(err)
	}
	if r.Numerator != -40 || r.Denominator != 1 {
		t.Errorf("expected -40/1, got %d/%d", r.Numerator, r.Denominator)
	}
}

func TestDoubleToRationalNegativeFraction(t *testing.T) {
	r, err := doubleToRational(-0.5)
	if err != nil {
		t.Fatal(err)
	}
	if r.Float64() != -0.5 {
		t.Errorf("expected -0.5, got %f", r.Float64())
	}
	if r.Numerator != -1 || r.Denominator != 2 {
		t.Errorf("expected -1/2, got %d/%d", r.Numerator, r.Denominator)
	}
}

func TestDoubleToRationalOverflow(t *testing.T) {
	_, err := doubleToRational(math.MaxFloat64)
	if err == nil {
		t.Fatal("expected error for overflow, got nil")
	}
}

// ===========================================================================
// Custom sheet names
// ===========================================================================

func TestLoadExcelCustomSheetNames(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	_ = f.SetSheetName("Sheet1", "MyChecks")
	for i, h := range checksHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("MyChecks", cell, h)
	}
	_ = f.SetCellValue("MyChecks", "B2", "Speed")
	_ = f.SetCellValue("MyChecks", "C2", "never_exceeds")
	_ = f.SetCellValue("MyChecks", "D2", 220)

	dir := t.TempDir()
	path := filepath.Join(dir, "custom.xlsx")
	_ = f.SaveAs(path)

	checks, err := LoadChecksFromExcel(path, WithChecksSheet("MyChecks"))
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
}

// ===========================================================================
// Extended CAN ID
// ===========================================================================

func TestLoadExcelDbcExtendedID(t *testing.T) {
	// Extended ID > 2047: must be marked Extended=TRUE.
	path := makeDbcWorkbook(t, [][]interface{}{
		{0x18FEF100, "J1939Msg", "TRUE", 8, "EngineSpeed", 0, 16, "little_endian", "FALSE", 0.125, 0, 0, 8031.875, "rpm"},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(dbc.Messages) != 1 {
		t.Fatalf("expected 1 message, got %d", len(dbc.Messages))
	}
	msg := dbc.Messages[0]
	if !msg.ID.IsExtended() {
		t.Error("expected extended CAN ID")
	}
	if msg.ID.Value() != 0x18FEF100 {
		t.Errorf("ID: got 0x%X, want 0x%X", msg.ID.Value(), 0x18FEF100)
	}
	if string(msg.Name) != "J1939Msg" {
		t.Errorf("Name: got %q", msg.Name)
	}
}

func TestLoadExcelDbcStandardAndExtendedMixed(t *testing.T) {
	// Mix of standard (Extended=FALSE) and extended (Extended=TRUE) messages.
	path := makeDbcWorkbook(t, [][]interface{}{
		{256, "StdMsg", "FALSE", 4, "Sig1", 0, 16, "little_endian", "FALSE", 1, 0, 0, 65535, ""},
		{0x18FF0100, "ExtMsg", "TRUE", 8, "Sig2", 0, 16, "big_endian", "FALSE", 1, 0, 0, 65535, ""},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(dbc.Messages) != 2 {
		t.Fatalf("expected 2 messages, got %d", len(dbc.Messages))
	}
	if dbc.Messages[0].ID.IsExtended() {
		t.Error("msg[0] should be standard")
	}
	if !dbc.Messages[1].ID.IsExtended() {
		t.Error("msg[1] should be extended")
	}
	if dbc.Messages[1].ID.Value() != 0x18FF0100 {
		t.Errorf("msg[1] ID: got 0x%X, want 0x18FF0100", dbc.Messages[1].ID.Value())
	}
}

func TestLoadExcelDbcLowIDExtended(t *testing.T) {
	// A low ID (< 2048) can still be extended if the column says so.
	path := makeDbcWorkbook(t, [][]interface{}{
		{100, "LowExtMsg", "TRUE", 8, "Sig", 0, 8, "little_endian", "FALSE", 1, 0, 0, 255, ""},
	})
	dbc, err := LoadDbcFromExcel(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !dbc.Messages[0].ID.IsExtended() {
		t.Error("expected extended CAN ID even though value < 2048")
	}
	if dbc.Messages[0].ID.Value() != 100 {
		t.Errorf("ID: got %d, want 100", dbc.Messages[0].ID.Value())
	}
}
