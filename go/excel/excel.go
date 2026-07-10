// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Package excel provides optional Excel-based loaders for Aletheia check
// definitions and DBC signal tables. It lives in its own module so the heavy
// excelize dependency (and its transitive crypto / net / text chain) stays
// off the critical path for consumers who drive the engine from YAML, code,
// or the Python/C++ bindings.
package excel

import (
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
	"github.com/xuri/excelize/v2"
)

// Option configures Excel loading behavior.
type Option func(*config)

type config struct {
	checksSheet   string
	whenThenSheet string
	dbcSheet      string
}

func defaultConfig() config {
	return config{
		checksSheet:   "Checks",
		whenThenSheet: "When-Then",
		dbcSheet:      "DBC",
	}
}

// WithChecksSheet sets the name of the simple-checks sheet.
func WithChecksSheet(name string) Option {
	return func(c *config) { c.checksSheet = name }
}

// WithWhenThenSheet sets the name of the when/then-checks sheet.
func WithWhenThenSheet(name string) Option {
	return func(c *config) { c.whenThenSheet = name }
}

// WithDBCSheet sets the name of the DBC definition sheet.
func WithDBCSheet(name string) Option {
	return func(c *config) { c.dbcSheet = name }
}

// ---------------------------------------------------------------------------
// Sheet headers
// ---------------------------------------------------------------------------

var (
	dbcHeaders = []string{
		"Message ID", "Message Name", "Extended", "DLC", "Signal", "Start Bit", "Length",
		"Byte Order", "Signed", "Factor", "Offset", "Min", "Max", "Unit",
		"Multiplexor", "Multiplex Value",
	}
	checksHeaders = []string{
		"Check Name", "Signal", "Condition", "Value", "Min", "Max",
		"Time (ms)", "Severity",
	}
	whenThenHeaders = []string{
		"Check Name", "When Signal", "When Condition", "When Value",
		"Then Signal", "Then Condition", "Then Value", "Then Min", "Then Max",
		"Within (ms)", "Severity",
	}
)

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

// LoadChecks loads signal checks from an Excel workbook.
// Reads the Checks and When-Then sheets. Either or both may be present.
func LoadChecks(path string, opts ...Option) ([]aletheia.CheckResult, error) {
	path = filepath.Clean(path)
	cfg := defaultConfig()
	for _, o := range opts {
		o(&cfg)
	}

	// Symlink + size + ZIP-bomb gates before excelize open.
	if err := validateLoaderPath(path, "excel"); err != nil {
		return nil, err
	}
	if err := checkFileSizeBound(path); err != nil {
		return nil, err
	}
	if err := checkXlsxUncompressedBound(path); err != nil {
		return nil, err
	}

	f, err := excelize.OpenFile(path)
	if err != nil {
		return nil, aletheia.WrapValidationError("opening Excel file", err)
	}
	defer f.Close()

	sheets := f.GetSheetList()
	hasChecks := containsString(sheets, cfg.checksSheet)
	hasWhenThen := containsString(sheets, cfg.whenThenSheet)

	if !hasChecks && !hasWhenThen {
		return nil, aletheia.NewValidationError(fmt.Sprintf("workbook has no '%s' or '%s' sheet", cfg.checksSheet, cfg.whenThenSheet))
	}

	var results []aletheia.CheckResult

	if hasChecks {
		simple, err := loadSimpleChecks(f, cfg.checksSheet)
		if err != nil {
			return nil, err
		}
		results = append(results, simple...)
	}

	if hasWhenThen {
		causal, err := loadWhenThenChecks(f, cfg.whenThenSheet)
		if err != nil {
			return nil, err
		}
		results = append(results, causal...)
	}

	return results, nil
}

// LoadDbc loads a DBC definition from the DBC sheet of an Excel workbook.
func LoadDbc(path string, opts ...Option) (*aletheia.DBCDefinition, error) {
	path = filepath.Clean(path)
	cfg := defaultConfig()
	for _, o := range opts {
		o(&cfg)
	}

	// Same hardening as LoadChecks.
	if err := validateLoaderPath(path, "excel"); err != nil {
		return nil, err
	}
	if err := checkFileSizeBound(path); err != nil {
		return nil, err
	}
	if err := checkXlsxUncompressedBound(path); err != nil {
		return nil, err
	}

	f, err := excelize.OpenFile(path)
	if err != nil {
		return nil, aletheia.WrapValidationError("opening Excel file", err)
	}
	defer f.Close()

	sheets := f.GetSheetList()
	if !containsString(sheets, cfg.dbcSheet) {
		return nil, aletheia.NewValidationError(fmt.Sprintf("workbook has no '%s' sheet", cfg.dbcSheet))
	}

	rows, err := readTypedRows(f, cfg.dbcSheet)
	if err != nil {
		return nil, err
	}

	dataRows := make([]map[string]xlsxCell, 0, len(rows))
	for _, d := range rows {
		if len(d) == 0 {
			continue // skip empty rows
		}
		dataRows = append(dataRows, d)
	}

	if len(dataRows) == 0 {
		return nil, aletheia.NewValidationError("dbc sheet must have a header row and at least one data row")
	}

	return parseDBCRows(dataRows)
}

// CreateTemplate creates a blank Excel template with headers and formatting.
// Does not overwrite existing files.
func CreateTemplate(path string) error {
	// Parent-dir gate before excelize.NewFile/SaveAs.
	if err := validateOutputParentDir(path); err != nil {
		return err
	}
	if _, err := os.Stat(path); err == nil {
		return aletheia.NewValidationError(fmt.Sprintf("file already exists: %s", path))
	}

	f := excelize.NewFile()
	defer f.Close()

	style, err := f.NewStyle(&excelize.Style{Font: &excelize.Font{Bold: true}})
	if err != nil {
		return aletheia.WrapValidationError("creating style", err)
	}

	// Default sheet is "Sheet1", rename to "DBC".
	if err := f.SetSheetName("Sheet1", "DBC"); err != nil {
		return aletheia.WrapValidationError("renaming sheet", err)
	}
	if err := writeHeaderRow(f, "DBC", dbcHeaders, style); err != nil {
		return err
	}

	if _, err := f.NewSheet("Checks"); err != nil {
		return aletheia.WrapValidationError("creating Checks sheet", err)
	}
	if err := writeHeaderRow(f, "Checks", checksHeaders, style); err != nil {
		return err
	}

	if _, err := f.NewSheet("When-Then"); err != nil {
		return aletheia.WrapValidationError("creating When-Then sheet", err)
	}
	if err := writeHeaderRow(f, "When-Then", whenThenHeaders, style); err != nil {
		return err
	}

	return f.SaveAs(path)
}

// ---------------------------------------------------------------------------
// Internal: sheet readers
// ---------------------------------------------------------------------------

// xlsxCell is a cell's trimmed string value plus whether it is stored as text
// (a shared / inline string). Strict coercion needs that distinction: a number
// stored as text is rejected for a numeric field. excelize reports a native
// number as CellTypeNumber (a saved file) or CellTypeUnset (an unsaved cell), a
// boolean as CellTypeBool, and text as CellTypeSharedString / CellTypeInlineString.
type xlsxCell struct {
	value  string
	isText bool
}

// readTypedRows returns one header→cell map per data row, holding only the
// present (non-empty) cells, each carrying its text-vs-native distinction. Every
// header column is read (position-independent lookup); a cell under an empty
// header is dropped.
func readTypedRows(f *excelize.File, sheet string) ([]map[string]xlsxCell, error) {
	grid, err := f.GetRows(sheet)
	if err != nil {
		return nil, aletheia.WrapValidationError(fmt.Sprintf("reading sheet %q", sheet), err)
	}
	if len(grid) == 0 {
		return nil, nil
	}
	headers := grid[0]
	rows := make([]map[string]xlsxCell, 0, len(grid)-1)
	for r := 1; r < len(grid); r++ {
		m := make(map[string]xlsxCell)
		for c, h := range headers {
			if h == "" || c >= len(grid[r]) {
				continue
			}
			val := strings.TrimSpace(grid[r][c])
			if val == "" {
				continue
			}
			coord, cerr := excelize.CoordinatesToCellName(c+1, r+1)
			if cerr != nil {
				return nil, aletheia.WrapValidationError("cell coordinate", cerr)
			}
			ct, cterr := f.GetCellType(sheet, coord)
			if cterr != nil {
				// Discarding this would default isText to false and let a
				// number-as-text cell slip past the strict numeric check.
				return nil, aletheia.WrapValidationError(fmt.Sprintf("cell type at %s", coord), cterr)
			}
			m[h] = xlsxCell{
				value:  val,
				isText: ct == excelize.CellTypeSharedString || ct == excelize.CellTypeInlineString,
			}
		}
		rows = append(rows, m)
	}
	return rows, nil
}

func writeHeaderRow(f *excelize.File, sheet string, headers []string, style int) error {
	for i, h := range headers {
		cell, err := excelize.CoordinatesToCellName(i+1, 1)
		if err != nil {
			return aletheia.WrapValidationError("cell name", err)
		}
		if err := f.SetCellValue(sheet, cell, h); err != nil {
			return aletheia.WrapValidationError("writing header", err)
		}
		if err := f.SetCellStyle(sheet, cell, cell, style); err != nil {
			return aletheia.WrapValidationError("setting style", err)
		}
	}
	return nil
}

func containsString(ss []string, target string) bool {
	for _, s := range ss {
		if s == target {
			return true
		}
	}
	return false
}

// ---------------------------------------------------------------------------
// Internal: simple checks
// ---------------------------------------------------------------------------

func loadSimpleChecks(f *excelize.File, sheet string) ([]aletheia.CheckResult, error) {
	rows, err := readTypedRows(f, sheet)
	if err != nil {
		return nil, err
	}
	var results []aletheia.CheckResult
	for rowIdx, d := range rows {
		rowNum := rowIdx + 2 // 1-indexed, skip header
		if len(d) == 0 {
			continue // skip empty rows
		}
		r, err := parseSimpleRow(d, rowNum)
		if err != nil {
			return nil, err
		}
		results = append(results, r)
	}
	return results, nil
}

func parseSimpleRow(d map[string]xlsxCell, rowNum int) (aletheia.CheckResult, error) {
	signal, err := xlsxStr(d, "Signal", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	condition, err := xlsxStr(d, "Condition", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}

	if !aletheia.IsSimpleCondition(condition) {
		return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: unknown condition '%s'", rowNum, condition))
	}

	var result aletheia.CheckResult

	switch {
	case aletheia.IsSimpleValueCondition(condition):
		v, err := xlsxRational(d, "Value", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = aletheia.DispatchSimple(signal, condition, v)
		if err != nil {
			return aletheia.CheckResult{}, err
		}

	case aletheia.IsSimpleRangeCondition(condition):
		if _, ok := d["Min"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: condition '%s' requires 'Min' and 'Max'", rowNum, condition))
		}
		if _, ok := d["Max"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: condition '%s' requires 'Min' and 'Max'", rowNum, condition))
		}
		lo, err := xlsxRational(d, "Min", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		hi, err := xlsxRational(d, "Max", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = aletheia.CheckSignal(signal).StaysBetween(lo, hi)
		if err != nil {
			return aletheia.CheckResult{}, err
		}

	case aletheia.IsSimpleSettlesCondition(condition):
		if _, ok := d["Min"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: condition 'settles_between' requires 'Min' and 'Max'", rowNum))
		}
		if _, ok := d["Max"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: condition 'settles_between' requires 'Min' and 'Max'", rowNum))
		}
		if _, ok := d["Time (ms)"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: condition 'settles_between' requires 'Time (ms)'", rowNum))
		}
		lo, err := xlsxRational(d, "Min", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		hi, err := xlsxRational(d, "Max", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		ms, err := xlsxInt(d, "Time (ms)", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = aletheia.CheckSignal(signal).SettlesBetween(lo, hi).Within(ms)
		if err != nil {
			return aletheia.CheckResult{}, err
		}

	case aletheia.IsSimpleEqualsCondition(condition):
		v, err := xlsxRational(d, "Value", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result = aletheia.CheckSignal(signal).Equals(v).Always()

	default:
		return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: unknown condition '%s'", rowNum, condition))
	}

	return applyMetadata(result, d), nil
}

// ---------------------------------------------------------------------------
// Internal: when/then checks
// ---------------------------------------------------------------------------

func loadWhenThenChecks(f *excelize.File, sheet string) ([]aletheia.CheckResult, error) {
	rows, err := readTypedRows(f, sheet)
	if err != nil {
		return nil, err
	}
	var results []aletheia.CheckResult
	for rowIdx, d := range rows {
		rowNum := rowIdx + 2
		if len(d) == 0 {
			continue
		}
		r, err := parseWhenThenRow(d, rowNum)
		if err != nil {
			return nil, err
		}
		results = append(results, r)
	}
	return results, nil
}

func parseWhenThenRow(d map[string]xlsxCell, rowNum int) (aletheia.CheckResult, error) {
	// When clause.
	whenSignal, err := xlsxStr(d, "When Signal", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	whenCond, err := xlsxStr(d, "When Condition", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	whenValue, err := xlsxRational(d, "When Value", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}

	if !aletheia.IsWhenCondition(whenCond) {
		return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: unknown when condition '%s'", rowNum, whenCond))
	}

	whenResult, err := aletheia.DispatchWhen(aletheia.CheckWhen(whenSignal), whenCond, whenValue)
	if err != nil {
		return aletheia.CheckResult{}, err
	}

	// Then clause.
	thenSignal, err := xlsxStr(d, "Then Signal", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	thenCond, err := xlsxStr(d, "Then Condition", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}

	if !aletheia.IsThenCondition(thenCond) {
		return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: unknown then condition '%s'", rowNum, thenCond))
	}

	withinMs, err := xlsxInt(d, "Within (ms)", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}

	thenBuilder := whenResult.Then(thenSignal)

	// Presence checks + value extraction stay loader-specific (column names and
	// error text differ per loader); the builder dispatch itself is shared.
	var thenValue, thenLo, thenHi aletheia.Rational
	switch thenCond {
	case "equals", "exceeds":
		v, err := xlsxRational(d, "Then Value", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		thenValue = v
	case "stays_between":
		if _, ok := d["Then Min"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: then condition 'stays_between' requires 'Then Min' and 'Then Max'", rowNum))
		}
		if _, ok := d["Then Max"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: then condition 'stays_between' requires 'Then Min' and 'Then Max'", rowNum))
		}
		lo, err := xlsxRational(d, "Then Min", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		hi, err := xlsxRational(d, "Then Max", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		thenLo, thenHi = lo, hi
	}
	result, err := aletheia.DispatchThen(thenBuilder, thenCond, thenValue, thenLo, thenHi, withinMs)
	if err != nil {
		return aletheia.CheckResult{}, err
	}

	return applyMetadata(result, d), nil
}

// ---------------------------------------------------------------------------
// Internal: DBC parsing
// ---------------------------------------------------------------------------

type messageKey struct {
	id       int64
	name     string
	extended bool
	dlc      int64
}

func parseDBCRows(rows []map[string]xlsxCell) (*aletheia.DBCDefinition, error) {
	type groupEntry struct {
		key     messageKey
		indices []int
	}

	groups := make(map[messageKey]*groupEntry)
	var insertionOrder []messageKey

	for idx, row := range rows {
		rowNum := idx + 2 // 1-indexed, skip header

		idCell, ok := row["Message ID"]
		if !ok {
			return nil, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid 'Message ID'", rowNum))
		}
		msgID, err := parseMessageID(idCell.value, rowNum)
		if err != nil {
			return nil, err
		}
		msgName, err := xlsxStr(row, "Message Name", rowNum)
		if err != nil {
			return nil, err
		}
		// 'Extended' is optional — an absent column (or empty cell) means a
		// standard 11-bit message, matching Python and C++.
		extended := false
		if _, ok := row["Extended"]; ok {
			extended, err = xlsxBool(row, "Extended", rowNum)
			if err != nil {
				return nil, err
			}
		}
		dlc, err := xlsxInt(row, "DLC", rowNum)
		if err != nil {
			return nil, err
		}

		key := messageKey{id: msgID, name: msgName, extended: extended, dlc: dlc}
		if g, exists := groups[key]; exists {
			g.indices = append(g.indices, idx)
		} else {
			groups[key] = &groupEntry{key: key, indices: []int{idx}}
			insertionOrder = append(insertionOrder, key)
		}
	}

	messages := make([]aletheia.DBCMessage, 0, len(insertionOrder))
	for _, key := range insertionOrder {
		g := groups[key]
		signals := make([]aletheia.DBCSignal, 0, len(g.indices))
		for _, i := range g.indices {
			sig, err := xlsxDBCSignal(rows[i], i+2)
			if err != nil {
				return nil, err
			}
			signals = append(signals, sig)
		}

		// Create the CAN ID based on the "Extended" column.
		var canID aletheia.CANID
		if key.extended {
			if key.id < 0 || key.id > aletheia.MaxExtendedID {
				return nil, aletheia.NewValidationError(fmt.Sprintf("extended CAN ID %d out of range [0, %d]", key.id, aletheia.MaxExtendedID))
			}
			eid, err := aletheia.NewExtendedID(uint32(key.id))
			if err != nil {
				return nil, err
			}
			canID = eid
		} else {
			if key.id < 0 || key.id > aletheia.MaxStandardID {
				return nil, aletheia.NewValidationError(fmt.Sprintf("standard CAN ID %d out of range [0, %d]", key.id, aletheia.MaxStandardID))
			}
			sid, err := aletheia.NewStandardID(uint16(key.id))
			if err != nil {
				return nil, err
			}
			canID = sid
		}

		if key.dlc < 0 || key.dlc > 15 {
			return nil, aletheia.NewValidationError(fmt.Sprintf("DLC %d out of range [0, 15]", key.dlc))
		}
		dlcVal, err := aletheia.NewDLC(uint8(key.dlc))
		if err != nil {
			return nil, err
		}

		messages = append(messages, aletheia.NewDBCMessage(
			canID,
			aletheia.MessageName(key.name),
			dlcVal,
			"",
			nil,
			signals,
		))
	}

	return aletheia.NewDBCDefinition("", messages), nil
}

func xlsxDBCSignal(row map[string]xlsxCell, rowNum int) (aletheia.DBCSignal, error) {
	name, err := xlsxStr(row, "Signal", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}

	startBit, err := xlsxInt(row, "Start Bit", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}
	if startBit < 0 || startBit > int64(aletheia.MaxBitPosition) {
		return aletheia.DBCSignal{}, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: 'Start Bit' %d out of range [0, %d]", rowNum, startBit, aletheia.MaxBitPosition))
	}

	length, err := xlsxInt(row, "Length", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}
	if length < 1 || length > int64(aletheia.MaxBitLength) {
		return aletheia.DBCSignal{}, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: 'Length' %d out of range [1, %d]", rowNum, length, aletheia.MaxBitLength))
	}

	byteOrderStr, err := xlsxStr(row, "Byte Order", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}
	var byteOrder aletheia.ByteOrder
	switch byteOrderStr {
	case "little_endian":
		byteOrder = aletheia.LittleEndian
	case "big_endian":
		byteOrder = aletheia.BigEndian
	default:
		return aletheia.DBCSignal{}, aletheia.NewValidationError(fmt.Sprintf("row %d: 'Byte Order' must be 'little_endian' or 'big_endian'", rowNum))
	}

	signed, err := xlsxBool(row, "Signed", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}

	factor, err := xlsxRational(row, "Factor", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}
	offset, err := xlsxRational(row, "Offset", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}
	minimum, err := xlsxRational(row, "Min", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}
	maximum, err := xlsxRational(row, "Max", rowNum)
	if err != nil {
		return aletheia.DBCSignal{}, err
	}

	// Unit is optional text; a non-text cell defaults to empty (matching the
	// Python reference's is_str check), not its stringified value.
	unit := ""
	if u, ok := row["Unit"]; ok && u.isText {
		unit = u.value
	}

	// Multiplexing.
	_, hasMuxor := row["Multiplexor"]
	_, hasMuxVal := row["Multiplex Value"]

	if hasMuxor != hasMuxVal {
		return aletheia.DBCSignal{}, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: 'Multiplexor' and 'Multiplex Value' must both be provided or both be empty",
			rowNum,
		))
	}

	var presence aletheia.SignalPresence
	if hasMuxor {
		muxor, err := xlsxStr(row, "Multiplexor", rowNum)
		if err != nil {
			return aletheia.DBCSignal{}, err
		}
		muxVal, err := xlsxInt(row, "Multiplex Value", rowNum)
		if err != nil {
			return aletheia.DBCSignal{}, err
		}
		if muxVal < 0 {
			return aletheia.DBCSignal{}, aletheia.NewValidationError(fmt.Sprintf(
				"row %d: 'Multiplex Value' must be non-negative, got %d", rowNum, muxVal))
		}
		presence = aletheia.Multiplexed{
			Multiplexor:     aletheia.SignalName(muxor),
			MultiplexValues: []aletheia.MultiplexValue{aletheia.MultiplexValue(muxVal)},
		}
	} else {
		presence = aletheia.AlwaysPresent{}
	}

	return aletheia.DBCSignal{
		Name:      aletheia.SignalName(name),
		StartBit:  aletheia.BitPosition(startBit),
		BitLength: aletheia.BitLength(length),
		ByteOrder: byteOrder,
		IsSigned:  signed,
		Factor:    factor,
		Offset:    offset,
		Minimum:   minimum,
		Maximum:   maximum,
		Unit:      aletheia.Unit(unit),
		Presence:  presence,
	}, nil
}

func parseMessageID(val string, rowNum int) (int64, error) {
	stripped := strings.TrimSpace(val)
	if strings.HasPrefix(strings.ToLower(stripped), "0x") {
		n, err := strconv.ParseInt(stripped[2:], 16, 64)
		if err != nil {
			return 0, aletheia.NewValidationError(fmt.Sprintf(
				"row %d: invalid 'Message ID' -- expected integer or hex string (e.g. 0x100)", rowNum))
		}
		return n, nil
	}
	n, err := strconv.ParseInt(stripped, 10, 64)
	if err != nil {
		return 0, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: invalid 'Message ID' -- expected integer or hex string (e.g. 0x100)", rowNum))
	}
	return n, nil
}

// ---------------------------------------------------------------------------
// Internal: cell value helpers
// ---------------------------------------------------------------------------

// xlsxStr requires a text cell — strict, matching the Python reference: a
// number or boolean cell is rejected rather than silently stringified.
func xlsxStr(d map[string]xlsxCell, key string, rowNum int) (string, error) {
	c, ok := d[key]
	if !ok || c.value == "" {
		return "", aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	if !c.isText {
		return "", aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be text, got a non-text value %q", rowNum, key, c.value))
	}
	return c.value, nil
}

// xlsxRational requires a TEXT-formatted numeric cell. A spreadsheet number
// cell stores an IEEE-754 double — lossy for decimals — so under the all-text
// contract a numeric value MUST be entered as text, and its exact literal is
// parsed by the kernel [aletheia.FromDecimal] (the cross-binding decimal SSOT:
// a decimal is an exact rational, never a float). A native number cell is
// rejected. RTS-gated (decimal parsing runs the kernel), so loading a workbook
// with numeric fields needs a live FFIBackend.
func xlsxRational(d map[string]xlsxCell, key string, rowNum int) (aletheia.Rational, error) {
	c, ok := d[key]
	if !ok || c.value == "" {
		return aletheia.Rational{}, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	if !c.isText {
		return aletheia.Rational{}, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: '%s' is a number cell (got %q); format it as TEXT so the exact value is preserved (a number cell stores a lossy float)",
			rowNum, key, c.value))
	}
	return aletheia.FromDecimal(strings.TrimSpace(c.value))
}

// xlsxInt requires a TEXT-formatted whole-number cell: the kernel
// [aletheia.FromDecimal] parses the literal exactly and a unit-denominator
// check rejects a fractional value. A native number cell is rejected (the
// all-text contract — see [xlsxRational]).
func xlsxInt(d map[string]xlsxCell, key string, rowNum int) (int64, error) {
	c, ok := d[key]
	if !ok || c.value == "" {
		return 0, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	if !c.isText {
		return 0, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: '%s' is a number cell (got %q); format it as TEXT so the exact value is preserved (a number cell stores a lossy float)",
			rowNum, key, c.value))
	}
	r, err := aletheia.FromDecimal(strings.TrimSpace(c.value))
	if err != nil {
		return 0, err
	}
	if r.Denominator != 1 {
		return 0, aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be a whole number, got %q", rowNum, key, c.value))
	}
	return r.Numerator, nil
}

// xlsxBool accepts the multi-form boolean Python's get_bool accepts: a native
// boolean, an integral 1/0, or TRUE/FALSE text (case-insensitive).
func xlsxBool(d map[string]xlsxCell, key string, rowNum int) (bool, error) {
	c, ok := d[key]
	if !ok || c.value == "" {
		return false, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	switch strings.ToLower(strings.TrimSpace(c.value)) {
	case "true", "1":
		return true, nil
	case "false", "0":
		return false, nil
	default:
		return false, aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be TRUE/FALSE or 1/0, got %q", rowNum, key, c.value))
	}
}

// applyMetadata sets optional name and severity from Excel row data (text cells
// only, matching Python's is_str check).
func applyMetadata(r aletheia.CheckResult, d map[string]xlsxCell) aletheia.CheckResult {
	if c, ok := d["Check Name"]; ok && c.isText && c.value != "" {
		r = r.Named(c.value)
	}
	if c, ok := d["Severity"]; ok && c.isText && c.value != "" {
		r = r.Severity(c.value)
	}
	return r
}
