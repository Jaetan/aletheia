// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package excel

import (
	"archive/zip"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"strconv"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
	"github.com/xuri/excelize/v2"
)

// TestMain brings the GHC runtime up once for the whole package. The Excel
// loaders parse every numeric cell through the kernel decimal SSOT
// (aletheia.FromDecimal), which is RTS-gated, so a throwaway FFIBackend's
// constructor runs hs_init and the RTS persists process-wide (hs_exit is never
// called). Best-effort: if the .so is absent, loader tests fail with the kernel's
// "runtime not initialized" error rather than silently passing.
func TestMain(m *testing.M) {
	if lib := findFFILib(); lib != "" {
		if _, err := aletheia.NewFFIBackend(lib); err != nil {
			fmt.Fprintf(os.Stderr, "TestMain: could not start GHC runtime: %v\n", err)
		}
	}
	os.Exit(m.Run())
}

// findFFILib locates libaletheia-ffi.so for the RTS bring-up: ALETHEIA_LIB env
// (operator / CI override) first, then the build-tree relative-path heuristic.
func findFFILib() string {
	if env := os.Getenv("ALETHEIA_LIB"); env != "" {
		if _, err := os.Stat(env); err == nil {
			return env
		}
	}
	for _, c := range []string{
		"../../build/libaletheia-ffi.so",
		"../build/libaletheia-ffi.so",
		"build/libaletheia-ffi.so",
	} {
		if abs, err := filepath.Abs(c); err == nil {
			if _, err := os.Stat(abs); err == nil {
				return abs
			}
		}
	}
	return ""
}

// cellText renders a test-row value as the TEXT string the all-text contract
// requires: under the decimal SSOT a numeric field MUST be a text cell (its
// exact literal parsed by aletheia.FromDecimal), so the workbook builders write
// every value as text. Floats use the 'f' format (no exponent) so the literal is
// a valid decimal grammar token.
func cellText(v any) string {
	switch x := v.(type) {
	case string:
		return x
	case int:
		return strconv.Itoa(x)
	case int64:
		return strconv.FormatInt(x, 10)
	case float64:
		return strconv.FormatFloat(x, 'f', -1, 64)
	case bool:
		if x {
			return "TRUE"
		}
		return "FALSE"
	default:
		return fmt.Sprintf("%v", x)
	}
}

// assertSameFormula compares two LTL formulas structurally. The Excel loader
// should produce the same formula as the reference check; this replaces a prior
// comparison via aletheia.FormatFormula (now internal — the public surface is the
// PropertyDiagnostic type) and is a stronger check than the old rendered-string
// equality.
func assertSameFormula(t *testing.T, want, got aletheia.Formula) {
	t.Helper()
	if !reflect.DeepEqual(want, got) {
		t.Errorf("formula mismatch:\n want: %#v\n  got: %#v", want, got)
	}
}

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

// requireErrorContains asserts err is a non-nil *aletheia.Error whose message
// contains substr. Duplicated from the main aletheia helpers because the excel
// module is a separate Go module with its own test tree.
func requireErrorContains(t *testing.T, err error, substr string) {
	t.Helper()
	if err == nil {
		t.Fatal("expected error, got nil")
	}
	var e *aletheia.Error
	if !errors.As(err, &e) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if !strings.Contains(err.Error(), substr) {
		t.Errorf("expected error containing %q, got: %v", substr, err)
	}
}

func makeChecksWorkbook(t *testing.T, rows [][]any) string {
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
			_ = f.SetCellValue("Checks", cell, cellText(val))
		}
	}
	path := filepath.Join(t.TempDir(), "test.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	return path
}

func makeWhenThenWorkbook(t *testing.T, rows [][]any) string {
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
			_ = f.SetCellValue("When-Then", cell, cellText(val))
		}
	}
	path := filepath.Join(t.TempDir(), "test.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	return path
}

func makeDBCWorkbook(t *testing.T, rows [][]any) string {
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
			_ = f.SetCellValue("DBC", cell, cellText(val))
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
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	assertSameFormula(t, aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220)).Formula(), checks[0].Formula())
}

func TestLoadExcelNeverBelow(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Voltage", "never_below", 11.5, nil, nil, nil, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	assertSameFormula(t, aletheia.CheckSignal("Voltage").NeverBelow(aletheia.Rational{Numerator: 23, Denominator: 2}).Formula(), checks[0].Formula())
}

func TestLoadExcelStaysBetween(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Voltage", "stays_between", nil, 11.5, 14.5, nil, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	reference, err := aletheia.CheckSignal("Voltage").StaysBetween(aletheia.Rational{Numerator: 23, Denominator: 2}, aletheia.Rational{Numerator: 29, Denominator: 2})
	if err != nil {
		t.Fatalf("StaysBetween: %v", err)
	}
	assertSameFormula(t, reference.Formula(), checks[0].Formula())
}

func TestLoadExcelNeverEquals(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "ErrorCode", "never_equals", 255, nil, nil, nil, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	assertSameFormula(t, aletheia.CheckSignal("ErrorCode").NeverEquals(aletheia.IntRational(255)).Formula(), checks[0].Formula())
}

func TestLoadExcelEqualsAlways(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Gear", "equals", 0, nil, nil, nil, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	assertSameFormula(t, aletheia.CheckSignal("Gear").Equals(aletheia.IntRational(0)).Always().Formula(), checks[0].Formula())
}

func TestLoadExcelSettlesBetween(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "CoolantTemp", "settles_between", nil, 80, 100, 5000, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	expected, _ := aletheia.CheckSignal("CoolantTemp").SettlesBetween(aletheia.IntRational(80), aletheia.IntRational(100)).Within(5000)
	assertSameFormula(t, expected.Formula(), checks[0].Formula())
}

func TestLoadExcelMultipleChecks(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil},
		{nil, "Voltage", "stays_between", nil, 11.5, 14.5, nil, nil},
	})
	checks, err := LoadChecks(path)
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
	path := makeWhenThenWorkbook(t, [][]any{
		{"Brake response", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, nil, nil, 100, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	expected, _ := aletheia.CheckWhen("BrakePedal").Exceeds(aletheia.IntRational(50)).Then("BrakeLight").Equals(aletheia.IntRational(1)).Within(100)
	assertSameFormula(t, expected.Formula(), checks[0].Formula())
}

func TestLoadExcelWhenEqualsThenExceeds(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]any{
		{nil, "Ignition", "equals", 1, "RPM", "exceeds", 500, nil, nil, 2000, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	expected, _ := aletheia.CheckWhen("Ignition").Equals(aletheia.IntRational(1)).Then("RPM").Exceeds(aletheia.IntRational(500)).Within(2000)
	assertSameFormula(t, expected.Formula(), checks[0].Formula())
}

func TestLoadExcelWhenDropsBelowThenStaysBetween(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]any{
		{nil, "FuelLevel", "drops_below", 10, "FuelWarning", "stays_between", nil, 1, 1, 50, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	expected, _ := aletheia.CheckWhen("FuelLevel").DropsBelow(aletheia.IntRational(10)).Then("FuelWarning").StaysBetween(aletheia.IntRational(1), aletheia.IntRational(1)).Within(50)
	assertSameFormula(t, expected.Formula(), checks[0].Formula())
}

// ===========================================================================
// Metadata
// ===========================================================================

func TestLoadExcelNameSet(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{"Speed limit", "Speed", "never_exceeds", 220, nil, nil, nil, nil},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].Name() != "Speed limit" {
		t.Errorf("Name: got %q, want %q", checks[0].Name(), "Speed limit")
	}
}

func TestLoadExcelSeveritySet(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Speed", "never_exceeds", 220, nil, nil, nil, "critical"},
	})
	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if checks[0].CheckSeverity() != "critical" {
		t.Errorf("Severity: got %q, want %q", checks[0].CheckSeverity(), "critical")
	}
}

func TestLoadExcelNameAndSeverity(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{"Speed limit", "Speed", "never_exceeds", 220, nil, nil, nil, "warning"},
	})
	checks, err := LoadChecks(path)
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
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil},
	})
	checks, err := LoadChecks(path)
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
	path := makeWhenThenWorkbook(t, [][]any{
		{"Brake response", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, nil, nil, 100, "safety"},
	})
	checks, err := LoadChecks(path)
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

func TestLoadExcelDBCSingleSignal(t *testing.T) {
	// id, name, extended, dlc, signal, startbit, length, byteorder, signed, factor, offset, min, max, unit
	path := makeDBCWorkbook(t, [][]any{
		{256, "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, "rpm"},
	})
	dbc, err := LoadDbc(path)
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
	if sig.ByteOrder != aletheia.LittleEndian {
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
	if _, ok := sig.Presence.(aletheia.AlwaysPresent); !ok {
		t.Errorf("Presence: expected AlwaysPresent, got %T", sig.Presence)
	}
}

func TestLoadExcelDBCMessageGrouping(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, "rpm"},
		{256, "EngineData", "FALSE", 8, "Temp", 16, 8, "little_endian", "FALSE", 1, -40, -40, 215, "C"},
		{512, "BrakeData", "FALSE", 4, "BrakePressure", 0, 16, "big_endian", "FALSE", 0.1, 0, 0, 6553.5, "bar"},
	})
	dbc, err := LoadDbc(path)
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

func TestLoadExcelDBCHexID(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{"0x100", "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, "rpm"},
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if dbc.Messages[0].ID.Value() != 0x100 {
		t.Errorf("ID: got %d, want %d", dbc.Messages[0].ID.Value(), 0x100)
	}
}

func TestLoadExcelDBCSignedTrue(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "EngineData", "FALSE", 8, "Temp", 0, 8, "little_endian", "TRUE", 1, -40, -40, 215, "C"},
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !dbc.Messages[0].Signals[0].IsSigned {
		t.Error("expected IsSigned=true")
	}
}

func TestLoadExcelDBCSignedIntegerOne(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "Msg", "FALSE", 8, "Sig", 0, 8, "little_endian", 1, 1, 0, 0, 255, ""},
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !dbc.Messages[0].Signals[0].IsSigned {
		t.Error("expected IsSigned=true for integer 1")
	}
}

func TestLoadExcelDBCSignedIntegerZero(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "Msg", "FALSE", 8, "Sig", 0, 8, "little_endian", 0, 1, 0, 0, 255, ""},
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if dbc.Messages[0].Signals[0].IsSigned {
		t.Error("expected IsSigned=false for integer 0")
	}
}

func TestLoadExcelDBCMissingUnit(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, nil},
	})
	dbc, err := LoadDbc(path)
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

func TestLoadExcelDBCAlwaysPresent(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", nil, nil},
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	sig := dbc.Messages[0].Signals[0]
	if _, ok := sig.Presence.(aletheia.AlwaysPresent); !ok {
		t.Errorf("expected AlwaysPresent, got %T", sig.Presence)
	}
}

func TestLoadExcelDBCMultiplexed(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "Msg", "FALSE", 8, "MuxSignal", 8, 8, "little_endian", "FALSE", 1, 0, 0, 255, "", "Selector", 3},
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	sig := dbc.Messages[0].Signals[0]
	mux, ok := sig.Presence.(aletheia.Multiplexed)
	if !ok {
		t.Fatalf("expected Multiplexed, got %T", sig.Presence)
	}
	if string(mux.Multiplexor) != "Selector" {
		t.Errorf("Multiplexor: got %q", mux.Multiplexor)
	}
	if len(mux.MultiplexValues) != 1 || mux.MultiplexValues[0] != 3 {
		t.Errorf("MultiplexValues: got %v", mux.MultiplexValues)
	}
}

func TestLoadExcelDBCMixedPresence(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "Msg", "FALSE", 8, "Selector", 0, 8, "little_endian", "FALSE", 1, 0, 0, 255, "", nil, nil},
		{256, "Msg", "FALSE", 8, "TempA", 8, 8, "little_endian", "FALSE", 1, -40, -40, 215, "C", "Selector", 0},
		{256, "Msg", "FALSE", 8, "TempB", 8, 8, "little_endian", "FALSE", 1, -40, -40, 215, "C", "Selector", 1},
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	msg := dbc.Messages[0]
	if len(msg.Signals) != 3 {
		t.Fatalf("expected 3 signals, got %d", len(msg.Signals))
	}
	if _, ok := msg.Signals[0].Presence.(aletheia.AlwaysPresent); !ok {
		t.Errorf("sig[0] expected AlwaysPresent, got %T", msg.Signals[0].Presence)
	}
	if mux, ok := msg.Signals[1].Presence.(aletheia.Multiplexed); !ok || string(mux.Multiplexor) != "Selector" || !aletheia.ContainsMuxValue(mux.MultiplexValues, 0) {
		t.Errorf("sig[1] expected Multiplexed(Selector, [0]), got %v", msg.Signals[1].Presence)
	}
	if mux, ok := msg.Signals[2].Presence.(aletheia.Multiplexed); !ok || string(mux.Multiplexor) != "Selector" || !aletheia.ContainsMuxValue(mux.MultiplexValues, 1) {
		t.Errorf("sig[2] expected Multiplexed(Selector, [1]), got %v", msg.Signals[2].Presence)
	}
}

func TestLoadExcelDBCPartialMuxError(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", "Selector", nil},
	})
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "must both be provided or both be empty")
}

func TestLoadExcelDBCPartialMuxValueOnlyError(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", nil, 3},
	})
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "must both be provided or both be empty")
}

// ===========================================================================
// Template creation
// ===========================================================================

func TestCreateExcelTemplateCreatesFile(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateTemplate(path); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if _, err := os.Stat(path); os.IsNotExist(err) {
		t.Fatal("template file not created")
	}
}

func TestCreateExcelTemplateSheetNames(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateTemplate(path); err != nil {
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

func TestCreateExcelTemplateDBCHeaders(t *testing.T) {
	dir := t.TempDir()
	path := filepath.Join(dir, "template.xlsx")
	if err := CreateTemplate(path); err != nil {
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
	if err := CreateTemplate(path); err != nil {
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
	if err := CreateTemplate(path); err != nil {
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
	if err := CreateTemplate(path); err != nil {
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
	if err := CreateTemplate(path); err != nil {
		t.Fatal(err)
	}
	err := CreateTemplate(path)
	requireErrorContains(t, err, "file already exists")
}

// ===========================================================================
// Error handling
// ===========================================================================

func TestLoadExcelFileNotFound(t *testing.T) {
	_, err := LoadChecks("/nonexistent/path/checks.xlsx")
	requireErrorContains(t, err, "excel file not found")
}

func TestLoadExcelDBCFileNotFound(t *testing.T) {
	_, err := LoadDbc("/nonexistent/path/dbc.xlsx")
	requireErrorContains(t, err, "excel file not found")
}

func TestLoadExcelNoChecksOrWhenThenSheet(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	_ = f.SetSheetName("Sheet1", "Other")
	dir := t.TempDir()
	path := filepath.Join(dir, "bad.xlsx")
	_ = f.SaveAs(path)

	_, err := LoadChecks(path)
	requireErrorContains(t, err, "no 'Checks' or 'When-Then' sheet")
}

func TestLoadExcelNoDBCSheet(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	_ = f.SetSheetName("Sheet1", "Other")
	dir := t.TempDir()
	path := filepath.Join(dir, "bad.xlsx")
	_ = f.SaveAs(path)

	_, err := LoadDbc(path)
	requireErrorContains(t, err, "no 'DBC' sheet")
}

func TestLoadExcelUnknownSimpleCondition(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Speed", "bogus", 100, nil, nil, nil, nil},
	})
	_, err := LoadChecks(path)
	requireErrorContains(t, err, "unknown condition 'bogus'")
}

func TestLoadExcelMissingValueForNeverExceeds(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Speed", "never_exceeds", nil, nil, nil, nil, nil},
	})
	_, err := LoadChecks(path)
	requireErrorContains(t, err, "missing or invalid 'Value'")
}

// TestLoadExcelRejectsOverflowValue is the Excel-side regression for the
// silent-clamp bug: a value whose exact rational overflows the Int64 wire range
// must make the loader FAIL (it dispatches through the kernel decimal SSOT, the
// same FromDecimal path as the YAML loader), not silently clamp. The value is a
// text cell carrying the literal verbatim — a float64 could not represent it.
func TestLoadExcelRejectsOverflowValue(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Speed", "never_exceeds", "99999999999999999999.5", nil, nil, nil, nil},
	})
	_, err := LoadChecks(path)
	requireErrorContains(t, err, "Int64 wire range")
}

func TestLoadExcelStaysBetweenMissingMin(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Voltage", "stays_between", nil, nil, 14.5, nil, nil},
	})
	_, err := LoadChecks(path)
	requireErrorContains(t, err, "requires 'Min' and 'Max'")
}

func TestLoadExcelSettlesBetweenMissingTime(t *testing.T) {
	path := makeChecksWorkbook(t, [][]any{
		{nil, "Temp", "settles_between", nil, 80, 100, nil, nil},
	})
	_, err := LoadChecks(path)
	requireErrorContains(t, err, "requires 'Time (ms)'")
}

func TestLoadExcelUnknownWhenCondition(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]any{
		{nil, "Brake", "bogus", 50, "BrakeLight", "equals", 1, nil, nil, 100, nil},
	})
	_, err := LoadChecks(path)
	requireErrorContains(t, err, "unknown when condition 'bogus'")
}

func TestLoadExcelUnknownThenCondition(t *testing.T) {
	path := makeWhenThenWorkbook(t, [][]any{
		{nil, "Brake", "exceeds", 50, "BrakeLight", "bogus", 1, nil, nil, 100, nil},
	})
	_, err := LoadChecks(path)
	requireErrorContains(t, err, "unknown then condition 'bogus'")
}

func TestLoadExcelInvalidByteOrder(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{256, "Msg", "FALSE", 8, "Sig", 0, 16, "mixed_endian", "FALSE", 1, 0, 0, 100, ""},
	})
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "Byte Order")
}

func TestLoadExcelInvalidMessageID(t *testing.T) {
	path := makeDBCWorkbook(t, [][]any{
		{"not_a_number", "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, ""},
	})
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "invalid 'Message ID'")
}

func TestLoadExcelDBCEmptyData(t *testing.T) {
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

	_, err := LoadDbc(path)
	// The error could be "at least one data row" or "no data rows" depending
	// on how excelize reports the sheet rows.
	requireErrorContains(t, err, "data row")
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
	_ = f.SetCellValue("Checks", "D2", "220")
	// Row 3: empty (skipped)
	// Row 4: Voltage never_below 11.5
	_ = f.SetCellValue("Checks", "B4", "Voltage")
	_ = f.SetCellValue("Checks", "C4", "never_below")
	_ = f.SetCellValue("Checks", "D4", "11.5")

	dir := t.TempDir()
	path := filepath.Join(dir, "gaps.xlsx")
	_ = f.SaveAs(path)

	checks, err := LoadChecks(path)
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
	_ = f.SetCellValue("Checks", "D2", "220")

	// When-Then sheet
	_, _ = f.NewSheet("When-Then")
	for i, h := range whenThenHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("When-Then", cell, h)
	}
	_ = f.SetCellValue("When-Then", "B2", "Brake")
	_ = f.SetCellValue("When-Then", "C2", "exceeds")
	_ = f.SetCellValue("When-Then", "D2", "50")
	_ = f.SetCellValue("When-Then", "E2", "BrakeLight")
	_ = f.SetCellValue("When-Then", "F2", "equals")
	_ = f.SetCellValue("When-Then", "G2", "1")
	_ = f.SetCellValue("When-Then", "J2", "100")

	dir := t.TempDir()
	path := filepath.Join(dir, "combined.xlsx")
	_ = f.SaveAs(path)

	checks, err := LoadChecks(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 2 {
		t.Fatalf("expected 2 checks, got %d", len(checks))
	}
	// First is simple check, second is when/then.
	assertSameFormula(t, aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220)).Formula(), checks[0].Formula())
	expected1, _ := aletheia.CheckWhen("Brake").Exceeds(aletheia.IntRational(50)).Then("BrakeLight").Equals(aletheia.IntRational(1)).Within(100)
	assertSameFormula(t, expected1.Formula(), checks[1].Formula())
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
	_ = f.SetCellValue("MyChecks", "D2", "220")

	dir := t.TempDir()
	path := filepath.Join(dir, "custom.xlsx")
	_ = f.SaveAs(path)

	checks, err := LoadChecks(path, WithChecksSheet("MyChecks"))
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

func TestLoadExcelDBCExtendedID(t *testing.T) {
	// Extended ID > 2047: must be marked Extended=TRUE.
	path := makeDBCWorkbook(t, [][]any{
		{0x18FEF100, "J1939Msg", "TRUE", 8, "EngineSpeed", 0, 16, "little_endian", "FALSE", 0.125, 0, 0, 8031.875, "rpm"},
	})
	dbc, err := LoadDbc(path)
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

func TestLoadExcelDBCStandardAndExtendedMixed(t *testing.T) {
	// Mix of standard (Extended=FALSE) and extended (Extended=TRUE) messages.
	path := makeDBCWorkbook(t, [][]any{
		{256, "StdMsg", "FALSE", 4, "Sig1", 0, 16, "little_endian", "FALSE", 1, 0, 0, 65535, ""},
		{0x18FF0100, "ExtMsg", "TRUE", 8, "Sig2", 0, 16, "big_endian", "FALSE", 1, 0, 0, 65535, ""},
	})
	dbc, err := LoadDbc(path)
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

func TestLoadExcelDBCLowIDExtended(t *testing.T) {
	// A low ID (< 2048) can still be extended if the column says so.
	path := makeDBCWorkbook(t, [][]any{
		{100, "LowExtMsg", "TRUE", 8, "Sig", 0, 8, "little_endian", "FALSE", 1, 0, 0, 255, ""},
	})
	dbc, err := LoadDbc(path)
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

// ---------------------------------------------------------------------------
// Adversarial-input hardening (cross-binding mirror)
// ---------------------------------------------------------------------------

func TestLoadChecks_RejectsSymlink(t *testing.T) {
	tmp := t.TempDir()
	real_ := filepath.Join(tmp, "real.xlsx")
	// Build a minimal valid .xlsx so the symlink target itself is loadable.
	f := excelize.NewFile()
	if err := f.SetSheetName("Sheet1", "Checks"); err != nil {
		t.Fatalf("SetSheetName: %v", err)
	}
	for i, h := range checksHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("Checks", cell, h)
	}
	_ = f.SetCellValue("Checks", "B2", "Speed")
	_ = f.SetCellValue("Checks", "C2", "never_exceeds")
	_ = f.SetCellValue("Checks", "D2", "220")
	if err := f.SaveAs(real_); err != nil {
		t.Fatalf("SaveAs: %v", err)
	}
	_ = f.Close()

	link := filepath.Join(tmp, "link.xlsx")
	if err := os.Symlink(real_, link); err != nil {
		t.Skip("symlink creation not permitted on this filesystem")
	}

	_, err := LoadChecks(link)
	requireErrorContains(t, err, "symbolic link")
}

func TestLoadChecks_RejectsOversize(t *testing.T) {
	tmp := t.TempDir()
	path := filepath.Join(tmp, "oversize.xlsx")
	// 65 MiB plain bytes — fails the raw-size cap before any ZIP parsing.
	chunk := make([]byte, 1024*1024)
	for i := range chunk {
		chunk[i] = 0xAA
	}
	out, err := os.Create(path)
	if err != nil {
		t.Fatalf("create: %v", err)
	}
	for i := 0; i < 65; i++ {
		if _, err := out.Write(chunk); err != nil {
			t.Fatalf("write: %v", err)
		}
	}
	_ = out.Close()

	_, err = LoadChecks(path)
	var bound *aletheia.InputBoundExceededError
	if !errors.As(err, &bound) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bound.BoundKind != aletheia.BoundKindInputLengthBytes {
		t.Errorf("BoundKind: got %s, want input_length_bytes", bound.BoundKind)
	}
	if bound.Limit != aletheia.MaxDBCTextBytes {
		t.Errorf("Limit: got %d, want %d", bound.Limit, aletheia.MaxDBCTextBytes)
	}
}

func TestLoadChecks_RejectsZipBomb(t *testing.T) {
	// Build a real ZIP with five entries totalling > MaxDBCTextBytes
	// uncompressed.  Each entry is highly compressible (all zeros) so the
	// archive on disk stays well under the raw cap; the central-directory
	// walker is what flags it.
	tmp := t.TempDir()
	path := filepath.Join(tmp, "bomb.xlsx")
	out, err := os.Create(path)
	if err != nil {
		t.Fatalf("create: %v", err)
	}
	zw := zip.NewWriter(out)
	zeros := make([]byte, 14*1024*1024) // 14 MiB
	for i := 0; i < 5; i++ {            // 5 × 14 MiB = 70 MiB > 64 MiB cap
		w, err := zw.CreateHeader(&zip.FileHeader{
			Name:   fmt.Sprintf("part-%d", i),
			Method: zip.Deflate,
		})
		if err != nil {
			t.Fatalf("CreateHeader: %v", err)
		}
		if _, err := w.Write(zeros); err != nil {
			t.Fatalf("Write: %v", err)
		}
	}
	if err := zw.Close(); err != nil {
		t.Fatalf("zw.Close: %v", err)
	}
	if err := out.Close(); err != nil {
		t.Fatalf("out.Close: %v", err)
	}

	_, err = LoadChecks(path)
	var bound *aletheia.InputBoundExceededError
	if !errors.As(err, &bound) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bound.BoundKind != aletheia.BoundKindInputLengthBytes {
		t.Errorf("BoundKind: got %s, want input_length_bytes", bound.BoundKind)
	}
}

func TestCreateTemplate_RejectsMissingParentDir(t *testing.T) {
	tmp := t.TempDir()
	bad := filepath.Join(tmp, "does_not_exist", "template.xlsx")
	err := CreateTemplate(bad)
	requireErrorContains(t, err, "parent directory does not exist")
}

// --- Strict-coercion + cross-binding portability locks (R3c) ----------------

// TestLoadExcelChecksRejectsNumberAsText locks the strict-coercion decision:
// a numeric field stored as TEXT must be rejected, not silently parsed. (The
// demo workbook can't exercise this — it stores numbers natively.)
// TestLoadExcelChecksRejectsNumberCell locks the all-text contract: a numeric
// field stored as a native NUMBER cell (a lossy float) is rejected — the exact
// value must be entered as text and parsed by the kernel decimal SSOT. Built
// inline because the workbook helpers stringify every value to text.
func TestLoadExcelChecksRejectsNumberCell(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	if err := f.SetSheetName("Sheet1", "Checks"); err != nil {
		t.Fatal(err)
	}
	for i, h := range checksHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("Checks", cell, h)
	}
	_ = f.SetCellValue("Checks", "B2", "Speed")
	_ = f.SetCellValue("Checks", "C2", "never_exceeds")
	_ = f.SetCellValue("Checks", "D2", 220) // native number cell → rejected
	path := filepath.Join(t.TempDir(), "checks.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	_, err := LoadChecks(path)
	requireErrorContains(t, err, "format it as TEXT")
}

// TestLoadExcelDBCRejectsNumberCell is the DBC-side all-text lock: the Factor
// stored as a native number cell is rejected (a lossy float). Built inline so
// only the Factor cell is a real number while every other field is text.
func TestLoadExcelDBCRejectsNumberCell(t *testing.T) {
	f := excelize.NewFile()
	defer f.Close()
	if err := f.SetSheetName("Sheet1", "DBC"); err != nil {
		t.Fatal(err)
	}
	for i, h := range dbcHeaders {
		cell, _ := excelize.CoordinatesToCellName(i+1, 1)
		_ = f.SetCellValue("DBC", cell, h)
	}
	textCells := map[string]string{
		"A2": "256", "B2": "M", "C2": "FALSE", "D2": "8", "E2": "Sig",
		"F2": "0", "G2": "8", "H2": "little_endian", "I2": "FALSE",
		"K2": "0", "L2": "0", "M2": "1", "N2": "u",
	}
	for cell, v := range textCells {
		_ = f.SetCellValue("DBC", cell, v)
	}
	_ = f.SetCellValue("DBC", "J2", 0.25) // Factor as a native number cell → rejected
	path := filepath.Join(t.TempDir(), "dbc.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "format it as TEXT")
}

// TestLoadExcelDemoWorkbookDBC is the cross-binding portability lock: the shared
// demo workbook's DBC sheet omits the Extended column, so every binding must
// load it as standard 11-bit messages (matching Python / C++ / Rust).
func TestLoadExcelDemoWorkbookDBC(t *testing.T) {
	p, err := filepath.Abs(filepath.Join("..", "..", "examples", "demo", "demo_workbook.xlsx"))
	if err != nil {
		t.Fatal(err)
	}
	dbc, err := LoadDbc(p)
	if err != nil {
		t.Fatalf("load demo DBC: %v", err)
	}
	if len(dbc.Messages) != 2 {
		t.Fatalf("expected 2 messages (EngineData, BrakeStatus), got %d", len(dbc.Messages))
	}
	for _, m := range dbc.Messages {
		if m.ID.IsExtended() {
			t.Errorf("message %q: absent Extended column must yield a standard message", string(m.Name))
		}
	}
}
