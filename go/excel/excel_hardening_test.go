// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package excel

import (
	"archive/zip"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
	"github.com/xuri/excelize/v2"
)

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
	// Past the size bound, so it is refused before the archive is read.
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
	if bound.Code != aletheia.CodeInputBoundExceeded {
		t.Errorf("Code: got %q, want %q", bound.Code, aletheia.CodeInputBoundExceeded)
	}
	if bound.Limit != aletheia.MaxDBCTextBytes {
		t.Errorf("Limit: got %d, want %d", bound.Limit, aletheia.MaxDBCTextBytes)
	}
}

func TestLoadChecks_RejectsZipBomb(t *testing.T) {
	// A real archive whose entries expand past the bound while the file on disk
	// stays far under it, so what refuses it is the index walk rather than the
	// size check before it.
	tmp := t.TempDir()
	path := filepath.Join(tmp, "bomb.xlsx")
	out, err := os.Create(path)
	if err != nil {
		t.Fatalf("create: %v", err)
	}
	zw := zip.NewWriter(out)
	// Five parts, each a quarter of the bound and a little more, so together
	// they pass it while every one of them compresses to almost nothing.
	const parts = 5
	zeros := make([]byte, aletheia.MaxDBCTextBytes/4)
	for i := 0; i < parts; i++ {
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
	if bound.Code != aletheia.CodeInputBoundExceeded {
		t.Errorf("Code: got %q, want %q", bound.Code, aletheia.CodeInputBoundExceeded)
	}
	// The refusal reports what the entries claim, not the bound plus one.
	if want := uint64(parts) * uint64(len(zeros)); bound.Observed != want {
		t.Errorf("observed: got %d, want %d, the size the entries claim", bound.Observed, want)
	}
	if bound.Limit != aletheia.MaxDBCTextBytes {
		t.Errorf("limit: got %d, want %d", bound.Limit, aletheia.MaxDBCTextBytes)
	}
}

func TestCreateTemplate_RejectsMissingParentDir(t *testing.T) {
	tmp := t.TempDir()
	bad := filepath.Join(tmp, "does_not_exist", "template.xlsx")
	err := CreateTemplate(bad)
	requireErrorContains(t, err, "parent directory does not exist")
}

// TestCreateTemplate_StatFailureNotMislabeled: a parent whose component is
// longer than a name may be makes the stat itself fail, which is not the
// directory being absent. Reporting it as absent would send a reader to create
// a directory that may well be there. The input path is held to the same
// distinction by TestLoadExcelStatFailureNotMislabeled, and the C++ binding to
// both. A name too long is the trigger because it needs no permissions.
func TestCreateTemplate_StatFailureNotMislabeled(t *testing.T) {
	bad := filepath.Join("/tmp", strings.Repeat("a", 5000), "template.xlsx")
	err := CreateTemplate(bad)
	requireErrorContains(t, err, "stat parent directory")
	if strings.Contains(err.Error(), "does not exist") {
		t.Errorf("stat failure mislabeled as an absent directory: %v", err)
	}
}

// TestLoadExcelChecksRejectsNumberCell: a numeric field stored as a number
// cell, which holds a float, is refused; the exact value is entered as text and
// the kernel parses the literal. Built cell by cell here, the workbook helpers
// writing every value as text.
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
	_ = f.SetCellValue("Checks", "D2", 220) // a number cell, which is refused
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
