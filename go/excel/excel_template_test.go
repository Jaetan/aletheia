// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package excel

import (
	"os"
	"path/filepath"
	"slices"
	"testing"

	"github.com/xuri/excelize/v2"
)

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

// TestCreateExcelTemplateHeaders: each sheet of the template opens with the
// header row its loader reads columns by name from.
func TestCreateExcelTemplateHeaders(t *testing.T) {
	path := filepath.Join(t.TempDir(), "template.xlsx")
	if err := CreateTemplate(path); err != nil {
		t.Fatal(err)
	}
	f, err := excelize.OpenFile(path)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()

	for _, c := range []struct {
		sheet string
		want  []string
	}{
		{"DBC", dbcHeaders},
		{"Checks", checksHeaders},
		{"When-Then", whenThenHeaders},
	} {
		t.Run(c.sheet, func(t *testing.T) {
			rows, err := f.GetRows(c.sheet)
			if err != nil {
				t.Fatalf("reading %s: %v", c.sheet, err)
			}
			if len(rows) < 1 {
				t.Fatalf("the %s sheet has no rows", c.sheet)
			}
			if !slices.Equal(rows[0], c.want) {
				t.Errorf("the %s header row is %q, want %q", c.sheet, rows[0], c.want)
			}
		})
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
