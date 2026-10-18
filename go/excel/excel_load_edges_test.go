// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package excel

import (
	"errors"
	"path/filepath"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
	"github.com/xuri/excelize/v2"
)

// TestLoadExcelRefusesARow: every row a loader refuses, and the sentence it
// refuses it with. A refusal names the field or the condition it is about, so a
// reader of the message knows which cell to go and fix.
func TestLoadExcelRefusesARow(t *testing.T) {
	checks := func(t *testing.T, row []any) error {
		t.Helper()
		_, err := LoadChecks(makeChecksWorkbook(t, [][]any{row}))
		return err
	}
	whenThen := func(t *testing.T, row []any) error {
		t.Helper()
		_, err := LoadChecks(makeWhenThenWorkbook(t, [][]any{row}))
		return err
	}
	dbc := func(t *testing.T, row []any) error {
		t.Helper()
		_, err := LoadDbc(makeDBCWorkbook(t, [][]any{row}))
		return err
	}

	for _, c := range []struct {
		name string
		load func(*testing.T, []any) error
		row  []any
		says string
	}{
		{
			name: "a condition no check carries",
			load: checks,
			row:  []any{nil, "Speed", "bogus", 100, nil, nil, nil, nil},
			says: "unknown condition 'bogus'",
		},
		{
			name: "a comparison with no value",
			load: checks,
			row:  []any{nil, "Speed", "never_exceeds", nil, nil, nil, nil, nil},
			says: "missing or invalid 'Value'",
		},
		{
			// A text cell holding only whitespace is an absent cell, as the
			// Python, C++ and Rust loaders read it.
			name: "a comparison whose value is only whitespace",
			load: checks,
			row:  []any{nil, "Speed", "never_exceeds", "  \t ", nil, nil, nil, nil},
			says: "missing or invalid 'Value'",
		},
		{
			name: "a range with no minimum",
			load: checks,
			row:  []any{nil, "Voltage", "stays_between", nil, nil, 14.5, nil, nil},
			says: "requires 'Min' and 'Max'",
		},
		{
			name: "a settling with no time",
			load: checks,
			row:  []any{nil, "Temp", "settles_between", nil, 80, 100, nil, nil},
			says: "requires 'Time (ms)'",
		},
		{
			// A whole-number field answers with the numerator of whatever it
			// parses, so without the refusal 100.5 milliseconds becomes 201.
			name: "a settling time written as a fraction",
			load: checks,
			row:  []any{nil, "Temp", "settles_between", nil, 80, 100, "100.5", nil},
			says: "'Time (ms)' must be a whole number",
		},
		{
			name: "a when condition no check leads with",
			load: whenThen,
			row:  []any{nil, "Brake", "bogus", 50, "BrakeLight", "equals", 1, nil, nil, 100, nil},
			says: "unknown when condition 'bogus'",
		},
		{
			name: "a then condition no check closes with",
			load: whenThen,
			row:  []any{nil, "Brake", "exceeds", 50, "BrakeLight", "bogus", 1, nil, nil, 100, nil},
			says: "unknown then condition 'bogus'",
		},
		{
			name: "a byte order that is neither",
			load: dbc,
			row:  []any{256, "Msg", "FALSE", 8, "Sig", 0, 16, "mixed_endian", "FALSE", 1, 0, 0, 100, ""},
			says: "Byte Order",
		},
		{
			name: "a message identifier that is not a number",
			load: dbc,
			row:  []any{"not_a_number", "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, ""},
			says: "invalid 'Message ID'",
		},
		{
			name: "a start bit written as a fraction",
			load: dbc,
			row:  []any{"0x100", "Engine", false, 8, "Speed", "1.5", 16, "little_endian", false, 1, 0, 0, 100, "rpm", nil, nil},
			says: "'Start Bit' must be a whole number",
		},
		{
			name: "a multiplexor with no value",
			load: dbc,
			row:  []any{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", "Selector", nil},
			says: "must both be provided or both be empty",
		},
		{
			name: "a multiplex value with no multiplexor",
			load: dbc,
			row:  []any{256, "Msg", "FALSE", 8, "Sig", 0, 16, "little_endian", "FALSE", 1, 0, 0, 100, "", nil, 3},
			says: "must both be provided or both be empty",
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			requireErrorContains(t, c.load(t, c.row), c.says)
		})
	}
}

// TestLoadExcelRefusesAValuePastTheWireRange: the value is a text cell carrying
// the literal, which no float could hold. The kernel reads it as past its
// component bound and refuses it, rather than clamping it, and the loader
// answers with the kernel's typed bound error located at the row and the
// column header.
func TestLoadExcelRefusesAValuePastTheWireRange(t *testing.T) {
	_, err := LoadChecks(makeChecksWorkbook(t, [][]any{
		{nil, "Speed", "never_exceeds", "99999999999999999999.5", nil, nil, nil, nil},
	}))
	var bound *aletheia.InputBoundExceededError
	if !errors.As(err, &bound) {
		t.Fatalf("expected *InputBoundExceededError, got %T: %v", err, err)
	}
	if bound.BoundKind != aletheia.BoundKindRationalComponentMagnitude {
		t.Errorf("BoundKind: got %s, want %s", bound.BoundKind, aletheia.BoundKindRationalComponentMagnitude)
	}
	if bound.Field != "decimal" {
		t.Errorf("Field: got %q, want %q", bound.Field, "decimal")
	}
	if bound.Location != "Row 2" || bound.Key != "Value" {
		t.Errorf("Location, Key: got %q, %q, want %q, %q", bound.Location, bound.Key, "Row 2", "Value")
	}
	if want := "Row 2: invalid 'Value': decimal: rational component magnitude"; !strings.HasPrefix(err.Error(), want) {
		t.Errorf("Error(): got %q, want it to start with %q", err.Error(), want)
	}
}

func TestLoadExcelFileNotFound(t *testing.T) {
	_, err := LoadChecks("/nonexistent/path/checks.xlsx")
	requireErrorContains(t, err, "excel file not found")
}

func TestLoadExcelDBCFileNotFound(t *testing.T) {
	_, err := LoadDbc("/nonexistent/path/dbc.xlsx")
	requireErrorContains(t, err, "excel file not found")
}

// TestLoadExcelStatFailureNotMislabeled: a path whose component is longer than
// a name may be makes the stat itself fail, which is not the same as the file
// being absent. The refusal says the stat failed, as the C++ and Rust loaders
// do, rather than reporting a file that is not there and hiding a machine under
// load. A name too long is the trigger because it needs no permissions.
func TestLoadExcelStatFailureNotMislabeled(t *testing.T) {
	long := "/tmp/" + strings.Repeat("a", 5000) + ".xlsx"
	_, err := LoadChecks(long)
	requireErrorContains(t, err, "stat excel file")
	if strings.Contains(err.Error(), "not found") {
		t.Errorf("stat failure mislabeled as 'not found': %v", err)
	}
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
