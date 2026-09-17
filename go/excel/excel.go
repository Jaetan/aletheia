// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Package excel provides optional Excel-based loaders for Aletheia check
// definitions and DBC signal tables. It lives in its own module so the heavy
// excelize dependency (and its transitive crypto / net / text chain) stays
// off the critical path for consumers who drive the engine from YAML, code,
// or the Python/C++ bindings.
package excel

import (
	"errors"
	"fmt"
	"math"
	"os"
	"path/filepath"
	"slices"
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

// openWorkbook applies the options and opens the file, holding it to the
// loaders' bounds first: a symbolic link is refused rather than followed, a
// file past the size bound is not read, and an archive that expands past the
// uncompressed bound is not opened. Every gate runs before excelize sees the
// path.
func openWorkbook(path string, opts []Option) (*excelize.File, config, error) {
	cfg := defaultConfig()
	for _, o := range opts {
		o(&cfg)
	}
	path = filepath.Clean(path)
	for _, gate := range []func() error{
		func() error { return validateLoaderPath(path, "excel") },
		func() error { return checkFileSizeBound(path) },
		func() error { return checkXlsxUncompressedBound(path) },
	} {
		if err := gate(); err != nil {
			return nil, cfg, err
		}
	}
	f, err := excelize.OpenFile(path)
	if err != nil {
		return nil, cfg, aletheia.WrapValidationError("opening Excel file", err)
	}
	return f, cfg, nil
}

// LoadChecks reads the checks a workbook carries, from its simple sheet, its
// when-then sheet, or both. One of the two must be present.
func LoadChecks(path string, opts ...Option) ([]aletheia.CheckResult, error) {
	f, cfg, err := openWorkbook(path, opts)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	sheets := f.GetSheetList()
	hasChecks := slices.Contains(sheets, cfg.checksSheet)
	hasWhenThen := slices.Contains(sheets, cfg.whenThenSheet)

	if !hasChecks && !hasWhenThen {
		return nil, aletheia.NewValidationError(fmt.Sprintf("workbook has no '%s' or '%s' sheet", cfg.checksSheet, cfg.whenThenSheet))
	}

	var results []aletheia.CheckResult

	if hasChecks {
		simple, err := loadRows(f, cfg.checksSheet, parseSimpleRow)
		if err != nil {
			return nil, err
		}
		results = append(results, simple...)
	}

	if hasWhenThen {
		causal, err := loadRows(f, cfg.whenThenSheet, parseWhenThenRow)
		if err != nil {
			return nil, err
		}
		results = append(results, causal...)
	}

	return results, nil
}

// LoadDbc loads a DBC definition from the DBC sheet of an Excel workbook.
func LoadDbc(path string, opts ...Option) (*aletheia.DBCDefinition, error) {
	f, cfg, err := openWorkbook(path, opts)
	if err != nil {
		return nil, err
	}
	defer f.Close()

	if !slices.Contains(f.GetSheetList(), cfg.dbcSheet) {
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

	if err := f.SaveAs(path); err != nil {
		return aletheia.WrapValidationError("writing the template", err)
	}
	return nil
}

// xlsxCell is what one cell holds, three ways: its trimmed display value, the
// value the file stores, and whether it is stored as text. The readers need the
// distinction, a number written as text being the only form they accept for a
// numeric field. The type comes from the cell's own attribute, which xlsx omits
// for its default numeric type, so a stored number reports no type at all;
// a boolean reports one, and text reports a shared or an inline string.
type xlsxCell struct {
	value  string
	raw    string
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
			raw, rerr := f.GetCellValue(sheet, coord, excelize.Options{RawCellValue: true})
			if rerr != nil {
				// Same fail-closed stance as the cell-type fetch: a missing
				// raw value would let a display rendering stand in for the
				// stored value on the strict numeric paths.
				return nil, aletheia.WrapValidationError(fmt.Sprintf("raw cell value at %s", coord), rerr)
			}
			m[h] = xlsxCell{
				value:  val,
				raw:    strings.TrimSpace(raw),
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

// loadRows builds one check per row a sheet carries, skipping the rows that
// carry nothing. A row is numbered as the workbook numbers it, the header
// being the first, so a refusal names a row the reader can go and look at.
func loadRows(f *excelize.File, sheet string, parse func(map[string]xlsxCell, int) (aletheia.CheckResult, error)) ([]aletheia.CheckResult, error) {
	rows, err := readTypedRows(f, sheet)
	if err != nil {
		return nil, err
	}
	var results []aletheia.CheckResult
	for i, row := range rows {
		if len(row) == 0 {
			continue
		}
		r, err := parse(row, i+2)
		if err != nil {
			return nil, err
		}
		results = append(results, r)
	}
	return results, nil
}

// requireColumns refuses a row lacking a column its condition needs, naming
// every column that condition takes rather than the first one that is absent.
func requireColumns(d map[string]xlsxCell, rowNum int, what, condition string, columns ...string) error {
	quoted := make([]string, len(columns))
	for i, c := range columns {
		quoted[i] = "'" + c + "'"
	}
	for _, c := range columns {
		if _, ok := d[c]; !ok {
			return aletheia.NewValidationError(fmt.Sprintf("row %d: %s '%s' requires %s",
				rowNum, what, condition, strings.Join(quoted, " and ")))
		}
	}
	return nil
}

// xlsxSimpleValues answers for the columns a simple check is written in,
// refusing in this loader's own words, which name the row.
type xlsxSimpleValues struct {
	d      map[string]xlsxCell
	rowNum int
	cond   string
}

func (v xlsxSimpleValues) Value() (aletheia.Rational, error) {
	return xlsxRational(v.d, "Value", v.rowNum)
}

func (v xlsxSimpleValues) Range() (aletheia.Rational, aletheia.Rational, error) {
	if err := requireColumns(v.d, v.rowNum, "condition", v.cond, "Min", "Max"); err != nil {
		return aletheia.Rational{}, aletheia.Rational{}, err
	}
	lo, err := xlsxRational(v.d, "Min", v.rowNum)
	if err != nil {
		return aletheia.Rational{}, aletheia.Rational{}, err
	}
	hi, err := xlsxRational(v.d, "Max", v.rowNum)
	if err != nil {
		return aletheia.Rational{}, aletheia.Rational{}, err
	}
	return lo, hi, nil
}

func (v xlsxSimpleValues) Within() (int64, error) {
	if err := requireColumns(v.d, v.rowNum, "condition", v.cond, "Time (ms)"); err != nil {
		return 0, err
	}
	return xlsxInt(v.d, "Time (ms)", v.rowNum)
}

// parseSimpleRow builds a check written as one signal and one condition. The
// word is held to the vocabulary here, before the dispatcher holds it again,
// so that the refusal names the row.
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

	result, err := aletheia.DispatchSimple(signal, condition,
		xlsxSimpleValues{d: d, rowNum: rowNum, cond: condition})
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	return applyMetadata(result, d), nil
}

// xlsxThenValues answers for the columns an obligation is written in.
type xlsxThenValues struct {
	d      map[string]xlsxCell
	rowNum int
	cond   string
}

func (v xlsxThenValues) Value() (aletheia.Rational, error) {
	return xlsxRational(v.d, "Then Value", v.rowNum)
}

func (v xlsxThenValues) Range() (aletheia.Rational, aletheia.Rational, error) {
	if err := requireColumns(v.d, v.rowNum, "then condition", v.cond, "Then Min", "Then Max"); err != nil {
		return aletheia.Rational{}, aletheia.Rational{}, err
	}
	lo, err := xlsxRational(v.d, "Then Min", v.rowNum)
	if err != nil {
		return aletheia.Rational{}, aletheia.Rational{}, err
	}
	hi, err := xlsxRational(v.d, "Then Max", v.rowNum)
	if err != nil {
		return aletheia.Rational{}, aletheia.Rational{}, err
	}
	return lo, hi, nil
}

func parseWhenThenRow(d map[string]xlsxCell, rowNum int) (aletheia.CheckResult, error) {
	// When clause, whose three conditions all read one value.
	whenSignal, err := xlsxStr(d, "When Signal", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	whenCond, err := xlsxStr(d, "When Condition", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	if !aletheia.IsWhenCondition(whenCond) {
		return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: unknown when condition '%s'", rowNum, whenCond))
	}
	whenValue, err := xlsxRational(d, "When Value", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
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

	result, err := aletheia.DispatchThen(whenResult.Then(thenSignal), thenCond,
		xlsxThenValues{d: d, rowNum: rowNum, cond: thenCond}, withinMs)
	if err != nil {
		return aletheia.CheckResult{}, err
	}

	return applyMetadata(result, d), nil
}

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
		msgID, err := parseMessageID(idCell, rowNum)
		if err != nil {
			return nil, err
		}
		msgName, err := xlsxStr(row, "Message Name", rowNum)
		if err != nil {
			return nil, err
		}
		// An absent column, or an empty cell, is a standard message, as it is
		// for the Python and the C++ loaders.
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

		// Past a byte the conversion below would truncate, and the constructor
		// would see a value the workbook never held; it refuses the rest.
		if key.dlc < 0 || key.dlc > math.MaxUint8 {
			return nil, aletheia.NewValidationError(fmt.Sprintf("DLC %d out of range", key.dlc))
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

// parseMessageID accepts a text cell holding a decimal or a hexadecimal
// literal, or a number cell whose stored value is a whole number. A number
// cell's grid value is its display, which a number format can round: a stored
// 256.7 under an integer format displays as "257". So the stored value is what
// is read.
func parseMessageID(c xlsxCell, rowNum int) (int64, error) {
	if c.isText {
		stripped := strings.TrimSpace(c.value)
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
	n, err := strconv.ParseInt(c.raw, 10, 64)
	switch {
	case errors.Is(err, strconv.ErrRange):
		return 0, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: invalid 'Message ID' -- number cell stores %q, which does not fit a 64-bit integer",
			rowNum, c.raw))
	case err != nil:
		// Anything the decimal reader refuses is not a whole number as stored:
		// a fraction, an exponent, or a hexadecimal literal, which needs a text
		// cell to be read as one.
		return 0, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: invalid 'Message ID' -- number cell stores %q, which is not a whole number (a hex ID needs a text cell)",
			rowNum, c.raw))
	}
	return n, nil
}

// xlsxCellAt answers what a row holds under one header, refusing a row that
// holds nothing there.
func xlsxCellAt(d map[string]xlsxCell, key string, rowNum int) (xlsxCell, error) {
	c, ok := d[key]
	if !ok || c.value == "" {
		return xlsxCell{}, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	return c, nil
}

// xlsxStr requires a text cell, as the Python loader does: a number or a
// boolean is refused rather than quietly turned into its own spelling.
func xlsxStr(d map[string]xlsxCell, key string, rowNum int) (string, error) {
	c, err := xlsxCellAt(d, key, rowNum)
	if err != nil {
		return "", err
	}
	if !c.isText {
		return "", aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be text, got a non-text value %q", rowNum, key, c.value))
	}
	return c.value, nil
}

// xlsxRational requires a number written as text, and the kernel parses the
// literal it was written as. A spreadsheet number cell stores a binary float,
// which cannot hold a decimal exactly, and every binding treats a decimal as an
// exact rational. Parsing runs the kernel, so a workbook with numeric fields
// needs a loaded library.
func xlsxRational(d map[string]xlsxCell, key string, rowNum int) (aletheia.Rational, error) {
	c, err := xlsxCellAt(d, key, rowNum)
	if err != nil {
		return aletheia.Rational{}, err
	}
	if !c.isText {
		// The stored value, not the grid's: a number format may have rounded
		// the display away from what the file holds.
		return aletheia.Rational{}, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: '%s' is a number cell (got %q); format it as TEXT so the exact value is preserved (a number cell stores a lossy float)",
			rowNum, key, c.raw))
	}
	r, err := aletheia.FromDecimal(strings.TrimSpace(c.value))
	if err != nil {
		// The kernel knows the literal and not the workbook, so the row and the
		// field are named here.
		return aletheia.Rational{}, aletheia.WrapValidationError(fmt.Sprintf("row %d: invalid '%s'", rowNum, key), err)
	}
	return r, nil
}

// xlsxInt is a rational whose denominator is one: the same cell, read the same
// way, with a fraction refused.
func xlsxInt(d map[string]xlsxCell, key string, rowNum int) (int64, error) {
	r, err := xlsxRational(d, key, rowNum)
	if err != nil {
		return 0, err
	}
	if r.Denominator != 1 {
		return 0, aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be a whole number, got %q", rowNum, key, d[key].value))
	}
	return r.Numerator, nil
}

// xlsxBool accepts what the Python loader accepts: a stored boolean, a number
// cell storing exactly one or zero, or the words true and false or the digits,
// in any case. The numeric form is read from the stored value, since a stored
// 1.4 can display as "1" and is not a boolean. A stored boolean passes the same
// test, xlsx holding it as exactly one or zero.
func xlsxBool(d map[string]xlsxCell, key string, rowNum int) (bool, error) {
	c, err := xlsxCellAt(d, key, rowNum)
	if err != nil {
		return false, err
	}
	if c.isText {
		switch strings.ToLower(strings.TrimSpace(c.value)) {
		case "true", "1":
			return true, nil
		case "false", "0":
			return false, nil
		default:
			return false, aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be TRUE/FALSE or 1/0, got %q", rowNum, key, c.value))
		}
	}
	switch c.raw {
	case "1":
		return true, nil
	case "0":
		return false, nil
	default:
		return false, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: '%s' must be TRUE/FALSE or 1/0, got a number cell storing %q (only exactly 1 or 0 is a boolean)",
			rowNum, key, c.raw))
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
