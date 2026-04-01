package aletheia

import (
	"fmt"
	"math"
	"os"
	"strconv"
	"strings"

	"github.com/xuri/excelize/v2"
)

// ExcelOption configures Excel loading behavior.
type ExcelOption func(*excelConfig)

type excelConfig struct {
	checksSheet   string
	whenThenSheet string
	dbcSheet      string
}

func defaultExcelConfig() excelConfig {
	return excelConfig{
		checksSheet:   "Checks",
		whenThenSheet: "When-Then",
		dbcSheet:      "DBC",
	}
}

// WithChecksSheet sets the name of the simple-checks sheet.
func WithChecksSheet(name string) ExcelOption {
	return func(c *excelConfig) { c.checksSheet = name }
}

// WithWhenThenSheet sets the name of the when/then-checks sheet.
func WithWhenThenSheet(name string) ExcelOption {
	return func(c *excelConfig) { c.whenThenSheet = name }
}

// WithDbcSheet sets the name of the DBC definition sheet.
func WithDbcSheet(name string) ExcelOption {
	return func(c *excelConfig) { c.dbcSheet = name }
}

// ---------------------------------------------------------------------------
// Sheet headers
// ---------------------------------------------------------------------------

var (
	dbcHeaders = []string{
		"Message ID", "Message Name", "DLC", "Signal", "Start Bit", "Length",
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

// LoadChecksFromExcel loads signal checks from an Excel workbook.
// Reads the Checks and When-Then sheets. Either or both may be present.
func LoadChecksFromExcel(path string, opts ...ExcelOption) ([]CheckResult, error) {
	cfg := defaultExcelConfig()
	for _, o := range opts {
		o(&cfg)
	}

	if _, err := os.Stat(path); os.IsNotExist(err) {
		return nil, fmt.Errorf("Excel file not found: %s", path)
	}

	f, err := excelize.OpenFile(path)
	if err != nil {
		return nil, fmt.Errorf("opening Excel file: %w", err)
	}
	defer f.Close()

	sheets := f.GetSheetList()
	hasChecks := containsString(sheets, cfg.checksSheet)
	hasWhenThen := containsString(sheets, cfg.whenThenSheet)

	if !hasChecks && !hasWhenThen {
		return nil, fmt.Errorf("Workbook has no '%s' or '%s' sheet", cfg.checksSheet, cfg.whenThenSheet)
	}

	var results []CheckResult

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

// LoadDbcFromExcel loads a DBC definition from the DBC sheet of an Excel workbook.
func LoadDbcFromExcel(path string, opts ...ExcelOption) (*DbcDefinition, error) {
	cfg := defaultExcelConfig()
	for _, o := range opts {
		o(&cfg)
	}

	if _, err := os.Stat(path); os.IsNotExist(err) {
		return nil, fmt.Errorf("Excel file not found: %s", path)
	}

	f, err := excelize.OpenFile(path)
	if err != nil {
		return nil, fmt.Errorf("opening Excel file: %w", err)
	}
	defer f.Close()

	sheets := f.GetSheetList()
	if !containsString(sheets, cfg.dbcSheet) {
		return nil, fmt.Errorf("Workbook has no '%s' sheet", cfg.dbcSheet)
	}

	rows, err := readSheetRows(f, cfg.dbcSheet)
	if err != nil {
		return nil, err
	}

	if len(rows) < 2 {
		return nil, fmt.Errorf("DBC sheet must have a header row and at least one data row")
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
		return nil, fmt.Errorf("DBC sheet has no data rows")
	}

	return parseDbcRows(dataRows)
}

// CreateExcelTemplate creates a blank Excel template with headers and formatting.
// Does not overwrite existing files.
func CreateExcelTemplate(path string) error {
	if _, err := os.Stat(path); err == nil {
		return fmt.Errorf("File already exists: %s", path)
	}

	f := excelize.NewFile()
	defer f.Close()

	style, err := f.NewStyle(&excelize.Style{Font: &excelize.Font{Bold: true}})
	if err != nil {
		return fmt.Errorf("creating style: %w", err)
	}

	// Default sheet is "Sheet1", rename to "DBC".
	if err := f.SetSheetName("Sheet1", "DBC"); err != nil {
		return fmt.Errorf("renaming sheet: %w", err)
	}
	if err := writeHeaderRow(f, "DBC", dbcHeaders, style); err != nil {
		return err
	}

	if _, err := f.NewSheet("Checks"); err != nil {
		return fmt.Errorf("creating Checks sheet: %w", err)
	}
	if err := writeHeaderRow(f, "Checks", checksHeaders, style); err != nil {
		return err
	}

	if _, err := f.NewSheet("When-Then"); err != nil {
		return fmt.Errorf("creating When-Then sheet: %w", err)
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
		return nil, fmt.Errorf("reading sheet %q: %w", sheet, err)
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
			return fmt.Errorf("cell name: %w", err)
		}
		if err := f.SetCellValue(sheet, cell, h); err != nil {
			return fmt.Errorf("writing header: %w", err)
		}
		if err := f.SetCellStyle(sheet, cell, cell, style); err != nil {
			return fmt.Errorf("setting style: %w", err)
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

func loadSimpleChecks(f *excelize.File, sheet string) ([]CheckResult, error) {
	rows, err := readSheetRows(f, sheet)
	if err != nil {
		return nil, err
	}
	if len(rows) == 0 {
		return nil, nil
	}

	headers := rows[0]
	var results []CheckResult
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

func parseSimpleRow(d map[string]string, rowNum int) (CheckResult, error) {
	signal, err := xlsxStr(d, "Signal", rowNum)
	if err != nil {
		return CheckResult{}, err
	}
	condition, err := xlsxStr(d, "Condition", rowNum)
	if err != nil {
		return CheckResult{}, err
	}

	if !allSimpleConditions[condition] {
		return CheckResult{}, fmt.Errorf("Row %d: unknown condition '%s'", rowNum, condition)
	}

	var result CheckResult

	switch {
	case simpleValueConditions[condition]:
		v, err := xlsxNumber(d, "Value", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		result, err = dispatchSimple(signal, condition, PhysicalValue(v))
		if err != nil {
			return CheckResult{}, err
		}

	case simpleRangeConditions[condition]:
		if _, ok := d["Min"]; !ok {
			return CheckResult{}, fmt.Errorf("Row %d: condition '%s' requires 'Min' and 'Max'", rowNum, condition)
		}
		if _, ok := d["Max"]; !ok {
			return CheckResult{}, fmt.Errorf("Row %d: condition '%s' requires 'Min' and 'Max'", rowNum, condition)
		}
		lo, err := xlsxNumber(d, "Min", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		hi, err := xlsxNumber(d, "Max", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		result = CheckSignal(signal).StaysBetween(PhysicalValue(lo), PhysicalValue(hi))

	case simpleSettlesConditions[condition]:
		if _, ok := d["Min"]; !ok {
			return CheckResult{}, fmt.Errorf("Row %d: condition 'settles_between' requires 'Min' and 'Max'", rowNum)
		}
		if _, ok := d["Max"]; !ok {
			return CheckResult{}, fmt.Errorf("Row %d: condition 'settles_between' requires 'Min' and 'Max'", rowNum)
		}
		if _, ok := d["Time (ms)"]; !ok {
			return CheckResult{}, fmt.Errorf("Row %d: condition 'settles_between' requires 'Time (ms)'", rowNum)
		}
		lo, err := xlsxNumber(d, "Min", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		hi, err := xlsxNumber(d, "Max", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		ms, err := xlsxInt(d, "Time (ms)", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		result, err = CheckSignal(signal).SettlesBetween(PhysicalValue(lo), PhysicalValue(hi)).Within(ms)
		if err != nil {
			return CheckResult{}, err
		}

	case simpleEqualsConditions[condition]:
		v, err := xlsxNumber(d, "Value", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		result = CheckSignal(signal).Equals(PhysicalValue(v)).Always()

	default:
		return CheckResult{}, fmt.Errorf("Row %d: unknown condition '%s'", rowNum, condition)
	}

	return applyExcelMetadata(result, d), nil
}

// ---------------------------------------------------------------------------
// Internal: when/then checks
// ---------------------------------------------------------------------------

func loadWhenThenChecks(f *excelize.File, sheet string) ([]CheckResult, error) {
	rows, err := readSheetRows(f, sheet)
	if err != nil {
		return nil, err
	}
	if len(rows) == 0 {
		return nil, nil
	}

	headers := rows[0]
	var results []CheckResult
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

func parseWhenThenRow(d map[string]string, rowNum int) (CheckResult, error) {
	// When clause.
	whenSignal, err := xlsxStr(d, "When Signal", rowNum)
	if err != nil {
		return CheckResult{}, err
	}
	whenCond, err := xlsxStr(d, "When Condition", rowNum)
	if err != nil {
		return CheckResult{}, err
	}
	whenValue, err := xlsxNumber(d, "When Value", rowNum)
	if err != nil {
		return CheckResult{}, err
	}

	if !whenConditions[whenCond] {
		return CheckResult{}, fmt.Errorf("Row %d: unknown when condition '%s'", rowNum, whenCond)
	}

	whenResult, err := dispatchWhen(CheckWhen(whenSignal), whenCond, PhysicalValue(whenValue))
	if err != nil {
		return CheckResult{}, err
	}

	// Then clause.
	thenSignal, err := xlsxStr(d, "Then Signal", rowNum)
	if err != nil {
		return CheckResult{}, err
	}
	thenCond, err := xlsxStr(d, "Then Condition", rowNum)
	if err != nil {
		return CheckResult{}, err
	}

	if !allThenConditions[thenCond] {
		return CheckResult{}, fmt.Errorf("Row %d: unknown then condition '%s'", rowNum, thenCond)
	}

	withinMs, err := xlsxInt(d, "Within (ms)", rowNum)
	if err != nil {
		return CheckResult{}, err
	}

	thenBuilder := whenResult.Then(thenSignal)

	var result CheckResult
	switch thenCond {
	case "equals":
		v, err := xlsxNumber(d, "Then Value", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		result, err = thenBuilder.Equals(PhysicalValue(v)).Within(withinMs)
		if err != nil {
			return CheckResult{}, err
		}
	case "exceeds":
		v, err := xlsxNumber(d, "Then Value", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		result, err = thenBuilder.Exceeds(PhysicalValue(v)).Within(withinMs)
		if err != nil {
			return CheckResult{}, err
		}
	case "stays_between":
		if _, ok := d["Then Min"]; !ok {
			return CheckResult{}, fmt.Errorf("Row %d: then condition 'stays_between' requires 'Then Min' and 'Then Max'", rowNum)
		}
		if _, ok := d["Then Max"]; !ok {
			return CheckResult{}, fmt.Errorf("Row %d: then condition 'stays_between' requires 'Then Min' and 'Then Max'", rowNum)
		}
		lo, err := xlsxNumber(d, "Then Min", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		hi, err := xlsxNumber(d, "Then Max", rowNum)
		if err != nil {
			return CheckResult{}, err
		}
		result, err = thenBuilder.StaysBetween(PhysicalValue(lo), PhysicalValue(hi)).Within(withinMs)
		if err != nil {
			return CheckResult{}, err
		}
	default:
		return CheckResult{}, fmt.Errorf("Row %d: unknown then condition '%s'", rowNum, thenCond)
	}

	return applyExcelMetadata(result, d), nil
}

// ---------------------------------------------------------------------------
// Internal: DBC parsing
// ---------------------------------------------------------------------------

type messageKey struct {
	id   int64
	name string
	dlc  int64
}

func parseDbcRows(rows []map[string]string) (*DbcDefinition, error) {
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
			return nil, fmt.Errorf("Row %d: missing or invalid 'Message ID'", rowNum)
		}
		msgID, err := parseMessageID(msgIDRaw, rowNum)
		if err != nil {
			return nil, err
		}
		msgName, err := xlsxStr(row, "Message Name", rowNum)
		if err != nil {
			return nil, err
		}
		dlc, err := xlsxInt(row, "DLC", rowNum)
		if err != nil {
			return nil, err
		}

		key := messageKey{id: msgID, name: msgName, dlc: dlc}
		if g, exists := groups[key]; exists {
			g.indices = append(g.indices, idx)
		} else {
			groups[key] = &groupEntry{key: key, indices: []int{idx}}
			insertionOrder = append(insertionOrder, key)
		}
	}

	messages := make([]DbcMessage, 0, len(insertionOrder))
	for _, key := range insertionOrder {
		g := groups[key]
		signals := make([]DbcSignal, 0, len(g.indices))
		for _, i := range g.indices {
			sig, err := xlsxDbcSignal(rows[i], i+2)
			if err != nil {
				return nil, err
			}
			signals = append(signals, sig)
		}

		// Create the CAN ID based on the range (standard if <= 2047).
		var canID CanID
		if key.id <= 2047 {
			sid, err := NewStandardID(uint16(key.id))
			if err != nil {
				return nil, fmt.Errorf("invalid CAN ID %d: %w", key.id, err)
			}
			canID = sid
		} else {
			eid, err := NewExtendedID(uint32(key.id))
			if err != nil {
				return nil, fmt.Errorf("invalid CAN ID %d: %w", key.id, err)
			}
			canID = eid
		}

		dlcVal, err := NewDLC(uint8(key.dlc))
		if err != nil {
			return nil, fmt.Errorf("invalid DLC %d: %w", key.dlc, err)
		}

		msg := DbcMessage{
			ID:      canID,
			Name:    MessageName(key.name),
			DLC:     dlcVal,
			Sender:  "",
			Signals: signals,
		}
		msg.buildSignalIndex()
		messages = append(messages, msg)
	}

	def := &DbcDefinition{
		Version:  "",
		Messages: messages,
	}
	def.buildIndexes()
	return def, nil
}

func xlsxDbcSignal(row map[string]string, rowNum int) (DbcSignal, error) {
	name, err := xlsxStr(row, "Signal", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}

	startBit, err := xlsxInt(row, "Start Bit", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}

	length, err := xlsxInt(row, "Length", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}

	byteOrderStr, err := xlsxStr(row, "Byte Order", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}
	var byteOrder ByteOrder
	switch byteOrderStr {
	case "little_endian":
		byteOrder = LittleEndian
	case "big_endian":
		byteOrder = BigEndian
	default:
		return DbcSignal{}, fmt.Errorf("Row %d: 'Byte Order' must be 'little_endian' or 'big_endian'", rowNum)
	}

	signed, err := xlsxBool(row, "Signed", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}

	factor, err := xlsxRational(row, "Factor", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}
	offset, err := xlsxRational(row, "Offset", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}
	minimum, err := xlsxRational(row, "Min", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}
	maximum, err := xlsxRational(row, "Max", rowNum)
	if err != nil {
		return DbcSignal{}, err
	}

	unit := ""
	if u, ok := row["Unit"]; ok {
		unit = u
	}

	// Multiplexing.
	_, hasMuxor := row["Multiplexor"]
	_, hasMuxVal := row["Multiplex Value"]

	if hasMuxor != hasMuxVal {
		return DbcSignal{}, fmt.Errorf(
			"Row %d: 'Multiplexor' and 'Multiplex Value' must both be provided or both be empty",
			rowNum,
		)
	}

	var presence SignalPresence
	if hasMuxor {
		muxor, err := xlsxStr(row, "Multiplexor", rowNum)
		if err != nil {
			return DbcSignal{}, err
		}
		muxVal, err := xlsxInt(row, "Multiplex Value", rowNum)
		if err != nil {
			return DbcSignal{}, err
		}
		presence = Multiplexed{
			Multiplexor: SignalName(muxor),
			MuxValue:    MultiplexValue(muxVal),
		}
	} else {
		presence = AlwaysPresent{}
	}

	return DbcSignal{
		Name:      SignalName(name),
		StartBit:  BitPosition(startBit),
		BitLength: BitLength(length),
		ByteOrder: byteOrder,
		IsSigned:  signed,
		Factor:    factor,
		Offset:    offset,
		Minimum:   minimum,
		Maximum:   maximum,
		Unit:      Unit(unit),
		Presence:  presence,
	}, nil
}

func parseMessageID(val string, rowNum int) (int64, error) {
	stripped := strings.TrimSpace(val)
	if strings.HasPrefix(strings.ToLower(stripped), "0x") {
		n, err := strconv.ParseInt(stripped[2:], 16, 64)
		if err != nil {
			return 0, fmt.Errorf(
				"Row %d: invalid 'Message ID' -- expected integer or hex string (e.g. 0x100)", rowNum)
		}
		return n, nil
	}
	n, err := strconv.ParseInt(stripped, 10, 64)
	if err != nil {
		return 0, fmt.Errorf(
			"Row %d: invalid 'Message ID' -- expected integer or hex string (e.g. 0x100)", rowNum)
	}
	return n, nil
}

// ---------------------------------------------------------------------------
// Internal: cell value helpers
// ---------------------------------------------------------------------------

func xlsxStr(d map[string]string, key string, rowNum int) (string, error) {
	v, ok := d[key]
	if !ok || v == "" {
		return "", fmt.Errorf("Row %d: missing or invalid '%s'", rowNum, key)
	}
	return v, nil
}

func xlsxNumber(d map[string]string, key string, rowNum int) (float64, error) {
	v, ok := d[key]
	if !ok || v == "" {
		return 0, fmt.Errorf("Row %d: missing or invalid '%s'", rowNum, key)
	}
	n, err := strconv.ParseFloat(v, 64)
	if err != nil {
		return 0, fmt.Errorf("Row %d: '%s' must be a number, got %q", rowNum, key, v)
	}
	return n, nil
}

func xlsxInt(d map[string]string, key string, rowNum int) (int64, error) {
	v, ok := d[key]
	if !ok || v == "" {
		return 0, fmt.Errorf("Row %d: missing or invalid '%s'", rowNum, key)
	}
	// Excel may serialize integers as "5000" or as "5000.0".
	// Try int first, then float.
	n, err := strconv.ParseInt(v, 10, 64)
	if err == nil {
		return n, nil
	}
	f, err := strconv.ParseFloat(v, 64)
	if err != nil {
		return 0, fmt.Errorf("Row %d: '%s' must be an integer, got %q", rowNum, key, v)
	}
	return int64(f), nil
}

func xlsxBool(d map[string]string, key string, rowNum int) (bool, error) {
	v, ok := d[key]
	if !ok || v == "" {
		return false, fmt.Errorf("Row %d: missing or invalid '%s'", rowNum, key)
	}
	lower := strings.ToLower(strings.TrimSpace(v))
	switch lower {
	case "true", "1":
		return true, nil
	case "false", "0":
		return false, nil
	default:
		return false, fmt.Errorf("Row %d: '%s' must be TRUE/FALSE or 1/0, got %q", rowNum, key, v)
	}
}

func xlsxRational(d map[string]string, key string, rowNum int) (Rational, error) {
	v, err := xlsxNumber(d, key, rowNum)
	if err != nil {
		return Rational{}, err
	}
	return doubleToRational(v), nil
}

// doubleToRational converts a float64 to a Rational.
// If the value is an exact integer, it uses denominator 1.
// Otherwise, it uses fixed precision (multiply by 10^6, simplify by GCD).
func doubleToRational(v float64) Rational {
	if v == math.Floor(v) && math.Abs(v) < 1e15 {
		return Rational{Numerator: int64(v), Denominator: 1}
	}
	const scale = 1_000_000
	num := int64(math.Round(v * scale))
	g := gcd64(abs64(num), scale)
	return Rational{Numerator: num / g, Denominator: scale / g}
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

// applyExcelMetadata sets optional name and severity from Excel row data.
func applyExcelMetadata(r CheckResult, d map[string]string) CheckResult {
	if name, ok := d["Check Name"]; ok && name != "" {
		r = r.Named(name)
	}
	if sev, ok := d["Severity"]; ok && sev != "" {
		r = r.Severity(sev)
	}
	return r
}
