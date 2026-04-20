// Package excel provides optional Excel-based loaders for Aletheia check
// definitions and DBC signal tables. It lives in its own module so the heavy
// excelize dependency (and its transitive crypto / net / text chain) stays
// off the critical path for consumers who drive the engine from YAML, code,
// or the Python/C++ bindings.
package excel

import (
	"fmt"
	"math"
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

// WithDbcSheet sets the name of the DBC definition sheet.
func WithDbcSheet(name string) Option {
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

	if _, err := os.Stat(path); os.IsNotExist(err) {
		return nil, aletheia.NewValidationError(fmt.Sprintf("excel file not found: %s", path))
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
func LoadDbc(path string, opts ...Option) (*aletheia.DbcDefinition, error) {
	path = filepath.Clean(path)
	cfg := defaultConfig()
	for _, o := range opts {
		o(&cfg)
	}

	if _, err := os.Stat(path); os.IsNotExist(err) {
		return nil, aletheia.NewValidationError(fmt.Sprintf("excel file not found: %s", path))
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

	rows, err := readSheetRows(f, cfg.dbcSheet)
	if err != nil {
		return nil, err
	}

	if len(rows) < 2 {
		return nil, aletheia.NewValidationError("dbc sheet must have a header row and at least one data row")
	}

	headers := rows[0]
	dataRows := make([]map[string]string, 0, len(rows)-1)
	for _, row := range rows[1:] {
		d := zipRow(headers, row)
		if len(d) == 0 {
			continue // skip empty rows
		}
		dataRows = append(dataRows, d)
	}

	if len(dataRows) == 0 {
		return nil, aletheia.NewValidationError("dbc sheet has no data rows")
	}

	return parseDbcRows(dataRows)
}

// CreateTemplate creates a blank Excel template with headers and formatting.
// Does not overwrite existing files.
func CreateTemplate(path string) error {
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

func readSheetRows(f *excelize.File, sheet string) ([][]string, error) {
	rows, err := f.GetRows(sheet)
	if err != nil {
		return nil, aletheia.WrapValidationError(fmt.Sprintf("reading sheet %q", sheet), err)
	}
	return rows, nil
}

func zipRow(headers, row []string) map[string]string {
	d := make(map[string]string)
	for i, h := range headers {
		if i < len(row) && strings.TrimSpace(row[i]) != "" {
			d[h] = strings.TrimSpace(row[i])
		}
	}
	return d
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
	rows, err := readSheetRows(f, sheet)
	if err != nil {
		return nil, err
	}
	if len(rows) == 0 {
		return nil, nil
	}

	headers := rows[0]
	var results []aletheia.CheckResult
	for rowIdx, row := range rows[1:] {
		rowNum := rowIdx + 2 // 1-indexed, skip header
		d := zipRow(headers, row)
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

func parseSimpleRow(d map[string]string, rowNum int) (aletheia.CheckResult, error) {
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
		v, err := xlsxNumber(d, "Value", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = aletheia.DispatchSimple(signal, condition, aletheia.PhysicalValue(v))
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
		lo, err := xlsxNumber(d, "Min", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		hi, err := xlsxNumber(d, "Max", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = aletheia.CheckSignal(signal).StaysBetween(aletheia.PhysicalValue(lo), aletheia.PhysicalValue(hi))
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
		lo, err := xlsxNumber(d, "Min", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		hi, err := xlsxNumber(d, "Max", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		ms, err := xlsxInt(d, "Time (ms)", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = aletheia.CheckSignal(signal).SettlesBetween(aletheia.PhysicalValue(lo), aletheia.PhysicalValue(hi)).Within(ms)
		if err != nil {
			return aletheia.CheckResult{}, err
		}

	case aletheia.IsSimpleEqualsCondition(condition):
		v, err := xlsxNumber(d, "Value", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result = aletheia.CheckSignal(signal).Equals(aletheia.PhysicalValue(v)).Always()

	default:
		return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: unknown condition '%s'", rowNum, condition))
	}

	return applyMetadata(result, d), nil
}

// ---------------------------------------------------------------------------
// Internal: when/then checks
// ---------------------------------------------------------------------------

func loadWhenThenChecks(f *excelize.File, sheet string) ([]aletheia.CheckResult, error) {
	rows, err := readSheetRows(f, sheet)
	if err != nil {
		return nil, err
	}
	if len(rows) == 0 {
		return nil, nil
	}

	headers := rows[0]
	var results []aletheia.CheckResult
	for rowIdx, row := range rows[1:] {
		rowNum := rowIdx + 2
		d := zipRow(headers, row)
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

func parseWhenThenRow(d map[string]string, rowNum int) (aletheia.CheckResult, error) {
	// When clause.
	whenSignal, err := xlsxStr(d, "When Signal", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	whenCond, err := xlsxStr(d, "When Condition", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}
	whenValue, err := xlsxNumber(d, "When Value", rowNum)
	if err != nil {
		return aletheia.CheckResult{}, err
	}

	if !aletheia.IsWhenCondition(whenCond) {
		return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: unknown when condition '%s'", rowNum, whenCond))
	}

	whenResult, err := aletheia.DispatchWhen(aletheia.CheckWhen(whenSignal), whenCond, aletheia.PhysicalValue(whenValue))
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

	var result aletheia.CheckResult
	switch thenCond {
	case "equals":
		v, err := xlsxNumber(d, "Then Value", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = thenBuilder.Equals(aletheia.PhysicalValue(v)).Within(withinMs)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
	case "exceeds":
		v, err := xlsxNumber(d, "Then Value", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = thenBuilder.Exceeds(aletheia.PhysicalValue(v)).Within(withinMs)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
	case "stays_between":
		if _, ok := d["Then Min"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: then condition 'stays_between' requires 'Then Min' and 'Then Max'", rowNum))
		}
		if _, ok := d["Then Max"]; !ok {
			return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: then condition 'stays_between' requires 'Then Min' and 'Then Max'", rowNum))
		}
		lo, err := xlsxNumber(d, "Then Min", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		hi, err := xlsxNumber(d, "Then Max", rowNum)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
		result, err = thenBuilder.StaysBetween(aletheia.PhysicalValue(lo), aletheia.PhysicalValue(hi)).Within(withinMs)
		if err != nil {
			return aletheia.CheckResult{}, err
		}
	default:
		return aletheia.CheckResult{}, aletheia.NewValidationError(fmt.Sprintf("row %d: unknown then condition '%s'", rowNum, thenCond))
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

func parseDbcRows(rows []map[string]string) (*aletheia.DbcDefinition, error) {
	type groupEntry struct {
		key     messageKey
		indices []int
	}

	groups := make(map[messageKey]*groupEntry)
	var insertionOrder []messageKey

	for idx, row := range rows {
		rowNum := idx + 2 // 1-indexed, skip header

		msgIDRaw, ok := row["Message ID"]
		if !ok {
			return nil, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid 'Message ID'", rowNum))
		}
		msgID, err := parseMessageID(msgIDRaw, rowNum)
		if err != nil {
			return nil, err
		}
		msgName, err := xlsxStr(row, "Message Name", rowNum)
		if err != nil {
			return nil, err
		}
		extended, err := xlsxBool(row, "Extended", rowNum)
		if err != nil {
			return nil, err
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

	messages := make([]aletheia.DbcMessage, 0, len(insertionOrder))
	for _, key := range insertionOrder {
		g := groups[key]
		signals := make([]aletheia.DbcSignal, 0, len(g.indices))
		for _, i := range g.indices {
			sig, err := xlsxDbcSignal(rows[i], i+2)
			if err != nil {
				return nil, err
			}
			signals = append(signals, sig)
		}

		// Create the CAN ID based on the "Extended" column.
		var canID aletheia.CanID
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

		messages = append(messages, aletheia.NewDbcMessage(
			canID,
			aletheia.MessageName(key.name),
			dlcVal,
			"",
			nil,
			signals,
		))
	}

	return aletheia.NewDbcDefinition("", messages), nil
}

func xlsxDbcSignal(row map[string]string, rowNum int) (aletheia.DbcSignal, error) {
	name, err := xlsxStr(row, "Signal", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}

	startBit, err := xlsxInt(row, "Start Bit", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}
	if startBit < 0 || startBit > int64(aletheia.MaxBitPosition) {
		return aletheia.DbcSignal{}, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: 'Start Bit' %d out of range [0, %d]", rowNum, startBit, aletheia.MaxBitPosition))
	}

	length, err := xlsxInt(row, "Length", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}
	if length < 1 || length > int64(aletheia.MaxBitLength) {
		return aletheia.DbcSignal{}, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: 'Length' %d out of range [1, %d]", rowNum, length, aletheia.MaxBitLength))
	}

	byteOrderStr, err := xlsxStr(row, "Byte Order", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}
	var byteOrder aletheia.ByteOrder
	switch byteOrderStr {
	case "little_endian":
		byteOrder = aletheia.LittleEndian
	case "big_endian":
		byteOrder = aletheia.BigEndian
	default:
		return aletheia.DbcSignal{}, aletheia.NewValidationError(fmt.Sprintf("row %d: 'Byte Order' must be 'little_endian' or 'big_endian'", rowNum))
	}

	signed, err := xlsxBool(row, "Signed", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}

	factor, err := xlsxRational(row, "Factor", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}
	offset, err := xlsxRational(row, "Offset", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}
	minimum, err := xlsxRational(row, "Min", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}
	maximum, err := xlsxRational(row, "Max", rowNum)
	if err != nil {
		return aletheia.DbcSignal{}, err
	}

	unit := ""
	if u, ok := row["Unit"]; ok {
		unit = u
	}

	// Multiplexing.
	_, hasMuxor := row["Multiplexor"]
	_, hasMuxVal := row["Multiplex Value"]

	if hasMuxor != hasMuxVal {
		return aletheia.DbcSignal{}, aletheia.NewValidationError(fmt.Sprintf(
			"row %d: 'Multiplexor' and 'Multiplex Value' must both be provided or both be empty",
			rowNum,
		))
	}

	var presence aletheia.SignalPresence
	if hasMuxor {
		muxor, err := xlsxStr(row, "Multiplexor", rowNum)
		if err != nil {
			return aletheia.DbcSignal{}, err
		}
		muxVal, err := xlsxInt(row, "Multiplex Value", rowNum)
		if err != nil {
			return aletheia.DbcSignal{}, err
		}
		if muxVal < 0 {
			return aletheia.DbcSignal{}, aletheia.NewValidationError(fmt.Sprintf(
				"row %d: 'Multiplex Value' must be non-negative, got %d", rowNum, muxVal))
		}
		presence = aletheia.Multiplexed{
			Multiplexor: aletheia.SignalName(muxor),
			MuxValues:   []aletheia.MultiplexValue{aletheia.MultiplexValue(muxVal)},
		}
	} else {
		presence = aletheia.AlwaysPresent{}
	}

	return aletheia.DbcSignal{
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

func xlsxStr(d map[string]string, key string, rowNum int) (string, error) {
	v, ok := d[key]
	if !ok || v == "" {
		return "", aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	return v, nil
}

func xlsxNumber(d map[string]string, key string, rowNum int) (float64, error) {
	v, ok := d[key]
	if !ok || v == "" {
		return 0, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	n, err := strconv.ParseFloat(v, 64)
	if err != nil {
		return 0, aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be a number, got %q", rowNum, key, v))
	}
	return n, nil
}

func xlsxInt(d map[string]string, key string, rowNum int) (int64, error) {
	v, ok := d[key]
	if !ok || v == "" {
		return 0, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	// Excel may serialize integers as "5000" or as "5000.0".
	// Try int first, then float.
	n, err := strconv.ParseInt(v, 10, 64)
	if err == nil {
		return n, nil
	}
	f, err := strconv.ParseFloat(v, 64)
	if err != nil {
		return 0, aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be an integer, got %q", rowNum, key, v))
	}
	if f != math.Floor(f) {
		return 0, aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be an integer, got %q", rowNum, key, v))
	}
	return int64(f), nil
}

func xlsxBool(d map[string]string, key string, rowNum int) (bool, error) {
	v, ok := d[key]
	if !ok || v == "" {
		return false, aletheia.NewValidationError(fmt.Sprintf("row %d: missing or invalid '%s'", rowNum, key))
	}
	lower := strings.ToLower(strings.TrimSpace(v))
	switch lower {
	case "true", "1":
		return true, nil
	case "false", "0":
		return false, nil
	default:
		return false, aletheia.NewValidationError(fmt.Sprintf("row %d: '%s' must be TRUE/FALSE or 1/0, got %q", rowNum, key, v))
	}
}

func xlsxRational(d map[string]string, key string, rowNum int) (aletheia.Rational, error) {
	v, err := xlsxNumber(d, key, rowNum)
	if err != nil {
		return aletheia.Rational{}, err
	}
	return doubleToRational(v)
}

// doubleToRational converts a float64 to a Rational.
// If the value is an exact integer, it uses denominator 1.
// Otherwise, it uses fixed precision (multiply by 10^6, simplify by GCD).
// Precision: 6 decimal digits (~1 ppm). Sufficient for DBC signal factors/offsets.
func doubleToRational(v float64) (aletheia.Rational, error) {
	if v == math.Floor(v) && math.Abs(v) < 1e15 {
		return aletheia.Rational{Numerator: int64(v), Denominator: 1}, nil
	}
	const scale = 1_000_000
	scaled := v * scale
	if scaled > math.MaxInt64 || scaled < math.MinInt64 || math.IsInf(scaled, 0) || math.IsNaN(scaled) {
		return aletheia.Rational{}, aletheia.NewValidationError(fmt.Sprintf("value %g overflows rational conversion", v))
	}
	num := int64(math.Round(scaled))
	g := gcd64(abs64(num), scale)
	return aletheia.Rational{Numerator: num / g, Denominator: scale / g}, nil
}

func gcd64(a, b int64) int64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

func abs64(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}

// applyMetadata sets optional name and severity from Excel row data.
func applyMetadata(r aletheia.CheckResult, d map[string]string) aletheia.CheckResult {
	if name, ok := d["Check Name"]; ok && name != "" {
		r = r.Named(name)
	}
	if sev, ok := d["Severity"]; ok && sev != "" {
		r = r.Severity(sev)
	}
	return r
}
