// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package excel

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"strconv"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
	"github.com/xuri/excelize/v2"
)

// runtimeDownEnv marks a child of TestLoadersBeforeAnyStart, in which TestMain
// starts nothing; its value is the checks workbook's path.
const runtimeDownEnv = "ALETHEIA_TEST_EXCEL_RUNTIME_DOWN"

// TestMain starts the GHC runtime once for the whole package. The Excel
// loaders parse every numeric cell but a DBC's message ID through the
// kernel's decimal parser (aletheia.FromDecimal), which needs the runtime
// up, and the runtime stays up for the process (hs_exit is never called).
// Best-effort: if the .so is absent, loader tests fail with the binding's
// "runtime not initialized" refusal rather than silently passing. A child of
// TestLoadersBeforeAnyStart starts nothing, its claim being about the runtime
// down.
func TestMain(m *testing.M) {
	if lib := findFFILib(); lib != "" && os.Getenv(runtimeDownEnv) == "" {
		if err := aletheia.StartRuntime(lib, 1, nil); err != nil {
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

// cellText writes a case's value the way the loaders read one, as text. A
// fraction is written without an exponent, an exponent not being a decimal the
// kernel reads.
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
// comparison, which is stronger than comparing two rendered strings.
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

// loadOne loads a workbook of a single row and answers the one check it holds.
func loadOne(t *testing.T, build func(*testing.T, [][]any) string, row []any) aletheia.CheckResult {
	t.Helper()
	checks, err := LoadChecks(build(t, [][]any{row}))
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if len(checks) != 1 {
		t.Fatalf("expected 1 check, got %d", len(checks))
	}
	return checks[0]
}

// mustCheck is a reference check built by the fluent builder, for comparing a
// loaded one against. A builder that refuses here is a mistake in the case, so
// it stops the run rather than failing one.
func mustCheck(r aletheia.CheckResult, err error) aletheia.CheckResult {
	if err != nil {
		panic(fmt.Sprintf("the reference check was refused: %v", err))
	}
	return r
}

// TestLoadExcelSimpleConditions: a row of the simple sheet builds the check the
// fluent builder of that condition builds. The columns are check name, signal,
// condition, value, minimum, maximum, time and severity.
func TestLoadExcelSimpleConditions(t *testing.T) {
	for _, c := range []struct {
		condition string
		row       []any
		want      func() aletheia.CheckResult
	}{
		{
			condition: "never_exceeds",
			row:       []any{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil},
			want: func() aletheia.CheckResult {
				return aletheia.CheckSignal("Speed").NeverExceeds(aletheia.IntRational(220))
			},
		},
		{
			condition: "never_below",
			row:       []any{nil, "Voltage", "never_below", 11.5, nil, nil, nil, nil},
			want: func() aletheia.CheckResult {
				return aletheia.CheckSignal("Voltage").NeverBelow(aletheia.Rational{Numerator: 23, Denominator: 2})
			},
		},
		{
			condition: "never_equals",
			row:       []any{nil, "ErrorCode", "never_equals", 255, nil, nil, nil, nil},
			want: func() aletheia.CheckResult {
				return aletheia.CheckSignal("ErrorCode").NeverEquals(aletheia.IntRational(255))
			},
		},
		{
			condition: "equals",
			row:       []any{nil, "Gear", "equals", 0, nil, nil, nil, nil},
			want: func() aletheia.CheckResult {
				return aletheia.CheckSignal("Gear").Equals(aletheia.IntRational(0)).Always()
			},
		},
		{
			condition: "stays_between",
			row:       []any{nil, "Voltage", "stays_between", nil, 11.5, 14.5, nil, nil},
			want: func() aletheia.CheckResult {
				return mustCheck(aletheia.CheckSignal("Voltage").StaysBetween(
					aletheia.Rational{Numerator: 23, Denominator: 2},
					aletheia.Rational{Numerator: 29, Denominator: 2}))
			},
		},
		{
			condition: "settles_between",
			row:       []any{nil, "CoolantTemp", "settles_between", nil, 80, 100, 5000, nil},
			want: func() aletheia.CheckResult {
				return mustCheck(aletheia.CheckSignal("CoolantTemp").
					SettlesBetween(aletheia.IntRational(80), aletheia.IntRational(100)).Within(5000))
			},
		},
	} {
		t.Run(c.condition, func(t *testing.T) {
			got := loadOne(t, makeChecksWorkbook, c.row)
			assertSameFormula(t, c.want().Formula(), got.Formula())
		})
	}
}

// TestLoadExcelWhenThenChecks: a row of the when-then sheet builds the check the
// fluent builder builds. The columns are check name, the when signal, condition
// and value, the then signal, condition, value, minimum and maximum, the time
// within which it must hold, and severity.
func TestLoadExcelWhenThenChecks(t *testing.T) {
	for _, c := range []struct {
		name string
		row  []any
		want func() aletheia.CheckResult
	}{
		{
			name: "exceeds then equals",
			row:  []any{"Brake response", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, nil, nil, 100, nil},
			want: func() aletheia.CheckResult {
				return mustCheck(aletheia.CheckWhen("BrakePedal").Exceeds(aletheia.IntRational(50)).
					Then("BrakeLight").Equals(aletheia.IntRational(1)).Within(100))
			},
		},
		{
			name: "equals then exceeds",
			row:  []any{nil, "Ignition", "equals", 1, "RPM", "exceeds", 500, nil, nil, 2000, nil},
			want: func() aletheia.CheckResult {
				return mustCheck(aletheia.CheckWhen("Ignition").Equals(aletheia.IntRational(1)).
					Then("RPM").Exceeds(aletheia.IntRational(500)).Within(2000))
			},
		},
		{
			name: "drops below then stays between",
			row:  []any{nil, "FuelLevel", "drops_below", 10, "FuelWarning", "stays_between", nil, 1, 1, 50, nil},
			want: func() aletheia.CheckResult {
				return mustCheck(aletheia.CheckWhen("FuelLevel").DropsBelow(aletheia.IntRational(10)).
					Then("FuelWarning").StaysBetween(aletheia.IntRational(1), aletheia.IntRational(1)).Within(50))
			},
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			got := loadOne(t, makeWhenThenWorkbook, c.row)
			assertSameFormula(t, c.want().Formula(), got.Formula())
		})
	}
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

// TestLoadExcelMetadata: the optional name and severity columns reach the check
// and are empty when the row leaves them out, on either sheet.
func TestLoadExcelMetadata(t *testing.T) {
	for _, c := range []struct {
		name         string
		build        func(*testing.T, [][]any) string
		row          []any
		wantName     string
		wantSeverity string
	}{
		{
			name:     "a name alone",
			build:    makeChecksWorkbook,
			row:      []any{"Speed limit", "Speed", "never_exceeds", 220, nil, nil, nil, nil},
			wantName: "Speed limit",
		},
		{
			name:         "a severity alone",
			build:        makeChecksWorkbook,
			row:          []any{nil, "Speed", "never_exceeds", 220, nil, nil, nil, "critical"},
			wantSeverity: "critical",
		},
		{
			name:         "both",
			build:        makeChecksWorkbook,
			row:          []any{"Speed limit", "Speed", "never_exceeds", 220, nil, nil, nil, "warning"},
			wantName:     "Speed limit",
			wantSeverity: "warning",
		},
		{
			name:  "neither",
			build: makeChecksWorkbook,
			row:   []any{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil},
		},
		{
			name:         "both, on the when-then sheet",
			build:        makeWhenThenWorkbook,
			row:          []any{"Brake response", "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, nil, nil, 100, "safety"},
			wantName:     "Brake response",
			wantSeverity: "safety",
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			got := loadOne(t, c.build, c.row)
			if got.Name() != c.wantName {
				t.Errorf("name: got %q, want %q", got.Name(), c.wantName)
			}
			if got.CheckSeverity() != c.wantSeverity {
				t.Errorf("severity: got %q, want %q", got.CheckSeverity(), c.wantSeverity)
			}
		})
	}
}

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

// TestLoadExcelDBCFields: one row of the DBC sheet, and what it sets on the
// definition the loader builds. The columns are the message identifier, name,
// whether it is extended and its length, then the signal's name, start bit,
// length, byte order, signedness, factor, offset, minimum, maximum and unit,
// and last the multiplexor and its value.
func TestLoadExcelDBCFields(t *testing.T) {
	for _, c := range []struct {
		name  string
		row   []any
		check func(*testing.T, *aletheia.DBCDefinition)
	}{
		{
			name: "a hexadecimal message identifier",
			row:  []any{"0x100", "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, "rpm"},
			check: func(t *testing.T, d *aletheia.DBCDefinition) {
				if got := d.Messages[0].ID.Value(); got != 0x100 {
					t.Errorf("identifier: got %d, want %d", got, 0x100)
				}
			},
		},
		{
			name: "the word TRUE is signed",
			row:  []any{256, "EngineData", "FALSE", 8, "Temp", 0, 8, "little_endian", "TRUE", 1, -40, -40, 215, "C"},
			check: func(t *testing.T, d *aletheia.DBCDefinition) {
				if !d.Messages[0].Signals[0].IsSigned {
					t.Error("the signal is unsigned, want signed")
				}
			},
		},
		{
			name: "the digit one is signed",
			row:  []any{256, "Msg", "FALSE", 8, "Sig", 0, 8, "little_endian", 1, 1, 0, 0, 255, ""},
			check: func(t *testing.T, d *aletheia.DBCDefinition) {
				if !d.Messages[0].Signals[0].IsSigned {
					t.Error("the signal is unsigned, want signed")
				}
			},
		},
		{
			name: "the digit zero is unsigned",
			row:  []any{256, "Msg", "FALSE", 8, "Sig", 0, 8, "little_endian", 0, 1, 0, 0, 255, ""},
			check: func(t *testing.T, d *aletheia.DBCDefinition) {
				if d.Messages[0].Signals[0].IsSigned {
					t.Error("the signal is signed, want unsigned")
				}
			},
		},
		{
			name: "an absent unit is empty",
			row:  []any{256, "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, nil},
			check: func(t *testing.T, d *aletheia.DBCDefinition) {
				if got := string(d.Messages[0].Signals[0].Unit); got != "" {
					t.Errorf("unit: got %q, want empty", got)
				}
			},
		},
		{
			name: "no multiplexor is always present",
			row:  []any{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", nil, nil},
			check: func(t *testing.T, d *aletheia.DBCDefinition) {
				if _, ok := d.Messages[0].Signals[0].Presence.(aletheia.AlwaysPresent); !ok {
					t.Errorf("presence is %T, want always present", d.Messages[0].Signals[0].Presence)
				}
			},
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			def, err := LoadDbc(makeDBCWorkbook(t, [][]any{c.row}))
			if err != nil {
				t.Fatalf("unexpected error: %v", err)
			}
			c.check(t, def)
		})
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
