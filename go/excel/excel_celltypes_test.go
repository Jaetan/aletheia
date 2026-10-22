// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package excel

import (
	"path/filepath"
	"strings"
	"testing"

	"github.com/xuri/excelize/v2"
)

// makeRawDBCWorkbook builds a single-row DBC workbook of text cells and hands
// it to the caller to overwrite the ones it wants stored as a number or a
// boolean, which the all-text helper cannot write.
func makeRawDBCWorkbook(t *testing.T, mutate func(f *excelize.File)) string {
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
	textCells := map[string]string{
		"A2": "256", "B2": "M", "C2": "FALSE", "D2": "8", "E2": "Sig",
		"F2": "0", "G2": "8", "H2": "little_endian", "I2": "FALSE",
		"J2": "1", "K2": "0", "L2": "0", "M2": "1", "N2": "u",
	}
	for cell, v := range textCells {
		_ = f.SetCellValue("DBC", cell, v)
	}
	mutate(f)
	path := filepath.Join(t.TempDir(), "dbc.xlsx")
	if err := f.SaveAs(path); err != nil {
		t.Fatal(err)
	}
	return path
}

// numFmtInteger gives a cell the integer number format, so that its display
// rounds what the file stores, which is the gap these tests are about.
func numFmtInteger(t *testing.T, f *excelize.File, cell string) {
	t.Helper()
	style, err := f.NewStyle(&excelize.Style{NumFmt: 1}) // built-in format "0"
	if err != nil {
		t.Fatal(err)
	}
	if err := f.SetCellStyle("DBC", cell, cell, style); err != nil {
		t.Fatal(err)
	}
}

// TestLoadExcelDBCRejectsFractionalStoredMessageID: a grid value is a display,
// so a cell storing 256.7 under the integer format displays as "257", and a
// loader reading the display would take a message identifier the file does not
// hold. The stored value is read, the fraction refused, and the message echoes
// what is stored rather than what is shown.
func TestLoadExcelDBCRejectsFractionalStoredMessageID(t *testing.T) {
	path := makeRawDBCWorkbook(t, func(f *excelize.File) {
		_ = f.SetCellValue("DBC", "A2", 256.7)
		numFmtInteger(t, f, "A2")
	})
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "invalid 'Message ID'")
	requireErrorContains(t, err, `"256.7"`)
	if err != nil && strings.Contains(err.Error(), `"257"`) {
		t.Errorf("error echoes the display rendering, want the raw stored value: %v", err)
	}
}

// TestLoadExcelDBCRejectsNonIntegralBoolCell: the same, for a boolean. A number
// cell is one only when it stores exactly one or zero, and a stored 1.4
// displays as "1", which a loader reading the display would take for true.
func TestLoadExcelDBCRejectsNonIntegralBoolCell(t *testing.T) {
	path := makeRawDBCWorkbook(t, func(f *excelize.File) {
		_ = f.SetCellValue("DBC", "I2", 1.4)
		numFmtInteger(t, f, "I2")
	})
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "'Signed'")
	requireErrorContains(t, err, `"1.4"`)
}

// TestLoadExcelDBCMessageIDNativeIntegerCell is the positive lock guarding the
// raw-value gate from over-rejecting: a native number cell whose raw stored
// value is exactly integral is a legitimate Message ID.
func TestLoadExcelDBCMessageIDNativeIntegerCell(t *testing.T) {
	path := makeRawDBCWorkbook(t, func(f *excelize.File) {
		_ = f.SetCellValue("DBC", "A2", 256)
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if dbc.Messages[0].ID.Value() != 256 {
		t.Errorf("ID: got %d, want 256", dbc.Messages[0].ID.Value())
	}
}

// TestLoadExcelDBCSignedNativeBoolCell: a native boolean cell stays a valid
// boolean under the raw-value gate (its raw stored value is exactly 1/0).
func TestLoadExcelDBCSignedNativeBoolCell(t *testing.T) {
	path := makeRawDBCWorkbook(t, func(f *excelize.File) {
		_ = f.SetCellValue("DBC", "I2", true)
	})
	dbc, err := LoadDbc(path)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}
	if !dbc.Messages[0].Signals[0].IsSigned {
		t.Error("expected IsSigned=true for a native TRUE cell")
	}
}

// TestLoadExcelDBCDecimalRefusalCarriesRowContext: a kernel decimal refusal
// surfaced through xlsxRational is located at the row and the column header,
// printed as "Row N: invalid 'Header': " before the kernel's message, so the
// operator can find the offending cell (the kernel knows the literal, not the
// workbook position).
func TestLoadExcelDBCDecimalRefusalCarriesRowContext(t *testing.T) {
	path := makeRawDBCWorkbook(t, func(f *excelize.File) {
		_ = f.SetCellValue("DBC", "J2", "abc") // Factor: text, not decimal grammar
	})
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "Row 2: invalid 'Factor': parse failed at line 1, column")
}

// TestLoadExcelDBCIntRefusalCarriesRowContext: same contract for the
// whole-number path (xlsxInt).
func TestLoadExcelDBCIntRefusalCarriesRowContext(t *testing.T) {
	path := makeRawDBCWorkbook(t, func(f *excelize.File) {
		_ = f.SetCellValue("DBC", "D2", "eight") // DLC: text, not decimal grammar
	})
	_, err := LoadDbc(path)
	requireErrorContains(t, err, "Row 2: invalid 'DLC': parse failed at line 1, column")
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
	if len(dbc.Messages) != 4 {
		t.Fatalf("expected 4 messages (VehicleDynamics, BrakeStatus, Powertrain, BodyStatus), got %d", len(dbc.Messages))
	}
	for _, m := range dbc.Messages {
		if m.ID.IsExtended() {
			t.Errorf("message %q: absent Extended column must yield a standard message", string(m.Name))
		}
	}
}
