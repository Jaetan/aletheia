package aletheia

import (
	"encoding/json"
	"fmt"
	"math"
)

// bytesToIntSlice converts []byte to []int for JSON serialization.
// Go's json.Marshal encodes []byte/[]uint8 as base64, but the Agda core
// expects a JSON array of integers: [0, 64, 31, ...].
func bytesToIntSlice(data []byte) []int {
	out := make([]int, len(data))
	for i, b := range data {
		out[i] = int(b)
	}
	return out
}

// --- Serialization (Go → JSON for Agda core) ---

func serializeCommand(command string, fields map[string]any) (string, error) {
	m := map[string]any{"type": "command", "command": command}
	for k, v := range fields {
		m[k] = v
	}
	b, err := json.Marshal(m)
	if err != nil {
		return "", protocolError("failed to serialize command: " + err.Error())
	}
	return string(b), nil
}

func serializeDataFrame(ts Timestamp, id CanID, dlc DLC, data FramePayload) (string, error) {
	m := map[string]any{
		"type":      "data",
		"timestamp": ts.Microseconds,
		"id":        id.Value(),
		"extended":  id.IsExtended(),
		"dlc":       dlc.Value(),
		"data":      bytesToIntSlice(data),
	}
	b, err := json.Marshal(m)
	if err != nil {
		return "", protocolError("failed to serialize data frame: " + err.Error())
	}
	return string(b), nil
}

func serializeDBC(dbc DbcDefinition) map[string]any {
	msgs := make([]map[string]any, 0, len(dbc.Messages))
	for _, msg := range dbc.Messages {
		sigs := make([]map[string]any, 0, len(msg.Signals))
		for _, sig := range msg.Signals {
			s := map[string]any{
				"name":     string(sig.Name),
				"startBit": sig.StartBit,
				"length":   sig.BitLength,
				"signed":   sig.IsSigned,
				"factor":   float64(sig.Factor),
				"offset":   float64(sig.Offset),
				"minimum":  float64(sig.Minimum),
				"maximum":  float64(sig.Maximum),
				"unit":     string(sig.Unit),
			}
			switch sig.ByteOrder {
			case BigEndian:
				s["byteOrder"] = "big_endian"
			case LittleEndian:
				s["byteOrder"] = "little_endian"
			default:
				panic(fmt.Sprintf("aletheia: invalid byte order %d", sig.ByteOrder))
			}
			if mux, ok := sig.Presence.(Multiplexed); ok {
				s["multiplexor"] = string(mux.Multiplexor)
				s["multiplex_value"] = mux.MuxValue
			}
			sigs = append(sigs, s)
		}
		m := map[string]any{
			"id":       msg.ID.Value(),
			"extended": msg.ID.IsExtended(),
			"name":     string(msg.Name),
			"dlc":      DlcToBytes(msg.DLC),
			"sender":   string(msg.Sender),
			"signals":  sigs,
		}
		msgs = append(msgs, m)
	}
	return map[string]any{
		"version":  dbc.Version,
		"messages": msgs,
	}
}

func serializeSignalValues(values []SignalValue) []map[string]any {
	result := make([]map[string]any, 0, len(values))
	for _, sv := range values {
		result = append(result, map[string]any{
			"name":  string(sv.Name),
			"value": float64(sv.Value),
		})
	}
	return result
}

func serializePredicate(p Predicate) map[string]any {
	switch p := p.(type) {
	case Equals:
		return map[string]any{"predicate": "equals", "signal": string(p.Signal), "value": float64(p.Value)}
	case LessThan:
		return map[string]any{"predicate": "lessThan", "signal": string(p.Signal), "value": float64(p.Value)}
	case GreaterThan:
		return map[string]any{"predicate": "greaterThan", "signal": string(p.Signal), "value": float64(p.Value)}
	case LessThanOrEqual:
		return map[string]any{"predicate": "lessThanOrEqual", "signal": string(p.Signal), "value": float64(p.Value)}
	case GreaterThanOrEqual:
		return map[string]any{"predicate": "greaterThanOrEqual", "signal": string(p.Signal), "value": float64(p.Value)}
	case Between:
		return map[string]any{"predicate": "between", "signal": string(p.Signal), "min": float64(p.Min), "max": float64(p.Max)}
	case ChangedBy:
		return map[string]any{"predicate": "changedBy", "signal": string(p.Signal), "delta": float64(p.Delta)}
	default:
		panic(fmt.Sprintf("aletheia: unknown predicate type %T", p))
	}
}

func serializeFormula(f Formula) map[string]any {
	switch f := f.(type) {
	case Atomic:
		return map[string]any{"operator": "atomic", "predicate": serializePredicate(f.Predicate)}
	case Not:
		return map[string]any{"operator": "not", "formula": serializeFormula(f.Inner)}
	case And:
		return map[string]any{"operator": "and", "left": serializeFormula(f.Left), "right": serializeFormula(f.Right)}
	case Or:
		return map[string]any{"operator": "or", "left": serializeFormula(f.Left), "right": serializeFormula(f.Right)}
	case Next:
		return map[string]any{"operator": "next", "formula": serializeFormula(f.Inner)}
	case Always:
		return map[string]any{"operator": "always", "formula": serializeFormula(f.Inner)}
	case Eventually:
		return map[string]any{"operator": "eventually", "formula": serializeFormula(f.Inner)}
	case Until:
		return map[string]any{"operator": "until", "left": serializeFormula(f.Left), "right": serializeFormula(f.Right)}
	case Release:
		return map[string]any{"operator": "release", "left": serializeFormula(f.Left), "right": serializeFormula(f.Right)}
	case MetricAlways:
		return map[string]any{"operator": "metricAlways", "timebound": f.Bound.Microseconds, "formula": serializeFormula(f.Inner)}
	case MetricEventually:
		return map[string]any{"operator": "metricEventually", "timebound": f.Bound.Microseconds, "formula": serializeFormula(f.Inner)}
	case MetricUntil:
		return map[string]any{"operator": "metricUntil", "timebound": f.Bound.Microseconds, "left": serializeFormula(f.Left), "right": serializeFormula(f.Right)}
	case MetricRelease:
		return map[string]any{"operator": "metricRelease", "timebound": f.Bound.Microseconds, "left": serializeFormula(f.Left), "right": serializeFormula(f.Right)}
	default:
		panic(fmt.Sprintf("aletheia: unknown formula type %T", f))
	}
}

// --- Deserialization (JSON from Agda core → Go) ---

// parseNumber handles the three number formats Agda emits:
// plain int, plain float, or {"numerator": n, "denominator": d}.
func parseNumber(v any) (float64, error) {
	switch n := v.(type) {
	case float64:
		return n, nil
	case map[string]any:
		num, ok1 := n["numerator"]
		den, ok2 := n["denominator"]
		if !ok1 || !ok2 {
			return 0, fmt.Errorf("expected {numerator, denominator}, got %v", n)
		}
		numF, err := parseNumber(num)
		if err != nil {
			return 0, err
		}
		denF, err := parseNumber(den)
		if err != nil {
			return 0, err
		}
		if denF == 0 {
			return 0, fmt.Errorf("zero denominator in rational")
		}
		return numF / denF, nil
	default:
		return 0, fmt.Errorf("expected number, got %T: %v", v, v)
	}
}

func parseNumberAsInt64(v any) (int64, error) {
	switch n := v.(type) {
	case float64:
		if n != math.Trunc(n) {
			return 0, fmt.Errorf("expected integer, got fractional: %v", n)
		}
		return int64(n), nil
	case map[string]any:
		num, ok1 := n["numerator"]
		den, ok2 := n["denominator"]
		if !ok1 || !ok2 {
			return 0, fmt.Errorf("expected {numerator, denominator}, got %v", n)
		}
		numI, err := parseNumberAsInt64(num)
		if err != nil {
			return 0, err
		}
		denI, err := parseNumberAsInt64(den)
		if err != nil {
			return 0, err
		}
		if denI == 0 {
			return 0, fmt.Errorf("zero denominator in rational")
		}
		if numI%denI != 0 {
			return 0, fmt.Errorf("expected integer, got non-exact rational %d/%d", numI, denI)
		}
		return numI / denI, nil
	default:
		return 0, fmt.Errorf("expected integer, got %T: %v", v, v)
	}
}

// getString returns the string value for key, or "" if missing or wrong type.
func getString(m map[string]any, key string) string {
	if v, ok := m[key]; ok {
		if s, ok := v.(string); ok {
			return s
		}
	}
	return ""
}

// getBool returns the bool value for key, or false if missing or wrong type.
func getBool(m map[string]any, key string) bool {
	if v, ok := m[key]; ok {
		if b, ok := v.(bool); ok {
			return b
		}
	}
	return false
}

// getArray returns the []any value for key, or nil if missing or wrong type.
func getArray(m map[string]any, key string) []any {
	if v, ok := m[key]; ok {
		if a, ok := v.([]any); ok {
			return a
		}
	}
	return nil
}

// getObject returns the map[string]any value for key, or nil if missing or wrong type.
func getObject(m map[string]any, key string) map[string]any {
	if v, ok := m[key]; ok {
		if o, ok := v.(map[string]any); ok {
			return o
		}
	}
	return nil
}

func parseResponse(raw string) (map[string]any, error) {
	var m map[string]any
	if err := json.Unmarshal([]byte(raw), &m); err != nil {
		return nil, protocolError("invalid JSON response: " + err.Error())
	}
	return m, nil
}

func checkErrorStatus(m map[string]any) error {
	status := getString(m, "status")
	if status == "error" {
		return protocolError(getString(m, "message"))
	}
	return nil
}

func parseSuccessResponse(raw string) error {
	m, err := parseResponse(raw)
	if err != nil {
		return err
	}
	if err := checkErrorStatus(m); err != nil {
		return err
	}
	status := getString(m, "status")
	if status == "success" {
		return nil
	}
	return protocolError("unexpected status: " + status)
}

func parseValidationResponse(raw string) (*ValidationResult, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "validation" {
		return nil, protocolError("expected validation response, got status: " + status)
	}

	var issues []ValidationIssue
	for _, item := range getArray(m, "issues") {
		issue, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in issues array")
		}
		sev := SeverityError
		if getString(issue, "severity") == "warning" {
			sev = SeverityWarning
		}
		code := IssueCode(getString(issue, "code"))
		if code == "" {
			code = IssueUnknown
		}
		issues = append(issues, ValidationIssue{
			Severity: sev,
			Code:     code,
			Detail:   getString(issue, "detail"),
		})
	}
	return &ValidationResult{
		HasErrors: getBool(m, "has_errors"),
		Issues:    issues,
	}, nil
}

func parseExtractionResponse(raw string) (*ExtractionResult, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "success" {
		return nil, protocolError("expected success response, got status: " + status)
	}

	var values []SignalValue
	for _, item := range getArray(m, "values") {
		v, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in values array")
		}
		val, err := parseNumber(v["value"])
		if err != nil {
			return nil, protocolError("invalid signal value: " + err.Error())
		}
		values = append(values, SignalValue{
			Name:  SignalName(getString(v, "name")),
			Value: PhysicalValue(val),
		})
	}

	var errors []SignalError
	for _, item := range getArray(m, "errors") {
		e, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in errors array")
		}
		errors = append(errors, SignalError{
			Name:  SignalName(getString(e, "name")),
			Error: getString(e, "error"),
		})
	}

	var absent []SignalName
	for _, item := range getArray(m, "absent") {
		s, ok := item.(string)
		if !ok {
			return nil, protocolError("expected string in absent array")
		}
		absent = append(absent, SignalName(s))
	}

	return &ExtractionResult{Values: values, Errors: errors, Absent: absent}, nil
}

func parseFrameDataResponse(raw string) (FramePayload, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "success" {
		return nil, protocolError("expected success response, got status: " + status)
	}

	data := getArray(m, "data")
	payload := make(FramePayload, len(data))
	for i, item := range data {
		f, err := parseNumber(item)
		if err != nil {
			return nil, protocolError("invalid byte in frame data: " + err.Error())
		}
		if f < 0 || f > 255 {
			return nil, protocolError(fmt.Sprintf("byte %d out of range: %v", i, f))
		}
		payload[i] = byte(f)
	}
	return payload, nil
}

func parseFrameResponse(raw string) (FrameResponse, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}

	status := getString(m, "status")
	switch status {
	case "ack":
		return Ack{}, nil
	case "violation":
		idx, err := parseNumberAsInt64(m["property_index"])
		if err != nil {
			return nil, protocolError("invalid property_index: " + err.Error())
		}
		if idx < 0 {
			return nil, protocolError(fmt.Sprintf("negative property_index: %d", idx))
		}
		ts, err := parseNumberAsInt64(m["timestamp"])
		if err != nil {
			return nil, protocolError("invalid timestamp: " + err.Error())
		}
		if ts < 0 {
			return nil, protocolError(fmt.Sprintf("negative timestamp: %d", ts))
		}
		reason := getString(m, "reason")
		return Violation{
			PropertyIndex: PropertyIndex(idx),
			Timestamp:     Timestamp{Microseconds: ts},
			Reason:        reason,
		}, nil
	case "error":
		return nil, protocolError(getString(m, "message"))
	default:
		return nil, protocolError("unexpected frame status: " + status)
	}
}

func parseStreamResponse(raw string) (*StreamResult, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}

	status := getString(m, "status")
	if status != "complete" {
		return nil, protocolError("expected complete response, got status: " + status)
	}

	var results []PropertyResult
	for _, item := range getArray(m, "results") {
		r, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in results array")
		}
		entryStatus := getString(r, "status")
		var verdict Verdict
		switch entryStatus {
		case "satisfaction":
			verdict = Holds
		case "violation":
			verdict = Fails
		default:
			return nil, protocolError("unknown verdict status: " + entryStatus)
		}

		idx, err := parseNumberAsInt64(r["property_index"])
		if err != nil {
			return nil, protocolError("invalid property_index: " + err.Error())
		}
		if idx < 0 {
			return nil, protocolError(fmt.Sprintf("negative property_index: %d", idx))
		}

		pr := PropertyResult{
			PropertyIndex: PropertyIndex(idx),
			Verdict:       verdict,
			Reason:        getString(r, "reason"),
		}

		if tsRaw, ok := r["timestamp"]; ok && tsRaw != nil {
			ts, err := parseNumberAsInt64(tsRaw)
			if err != nil {
				return nil, protocolError("invalid timestamp in result: " + err.Error())
			}
			if ts < 0 {
				return nil, protocolError(fmt.Sprintf("negative timestamp in result: %d", ts))
			}
			t := Timestamp{Microseconds: ts}
			pr.Timestamp = &t
		}

		results = append(results, pr)
	}
	return &StreamResult{Results: results}, nil
}

func parseDbcResponse(raw string) (*DbcDefinition, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}

	dbcRaw := getObject(m, "dbc")
	if dbcRaw == nil {
		return nil, protocolError("missing 'dbc' field in response")
	}
	return parseDbcDefinition(dbcRaw)
}

func parseDbcDefinition(j map[string]any) (*DbcDefinition, error) {
	var messages []DbcMessage
	for _, item := range getArray(j, "messages") {
		mRaw, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in messages array")
		}
		msg, err := parseDbcMessage(mRaw)
		if err != nil {
			return nil, err
		}
		messages = append(messages, *msg)
	}
	return &DbcDefinition{
		Version:  getString(j, "version"),
		Messages: messages,
	}, nil
}

func parseDbcMessage(j map[string]any) (*DbcMessage, error) {
	idVal, err := parseNumber(j["id"])
	if err != nil {
		return nil, protocolError("invalid message id: " + err.Error())
	}
	extended := getBool(j, "extended")

	var id CanID
	if extended {
		eid, err := NewExtendedID(uint32(idVal))
		if err != nil {
			return nil, protocolError(err.Error())
		}
		id = eid
	} else {
		if idVal > math.MaxUint16 {
			return nil, protocolError(fmt.Sprintf("standard CAN ID %v exceeds uint16 range", idVal))
		}
		sid, err := NewStandardID(uint16(idVal))
		if err != nil {
			return nil, protocolError(err.Error())
		}
		id = sid
	}

	dlcVal, err := parseNumber(j["dlc"])
	if err != nil {
		return nil, protocolError("invalid DLC: " + err.Error())
	}
	dlc, err := BytesToDlc(int(dlcVal))
	if err != nil {
		return nil, protocolError(err.Error())
	}

	var signals []DbcSignal
	for _, item := range getArray(j, "signals") {
		sRaw, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in signals array")
		}
		sig, err := parseDbcSignal(sRaw)
		if err != nil {
			return nil, err
		}
		signals = append(signals, sig)
	}

	return &DbcMessage{
		ID:      id,
		Name:    MessageName(getString(j, "name")),
		DLC:     dlc,
		Sender:  NodeName(getString(j, "sender")),
		Signals: signals,
	}, nil
}

func parseDbcSignal(j map[string]any) (DbcSignal, error) {
	var zero DbcSignal
	bo := LittleEndian
	if getString(j, "byteOrder") == "big_endian" {
		bo = BigEndian
	}

	factor, err := parseNumber(j["factor"])
	if err != nil {
		return zero, protocolError("invalid factor: " + err.Error())
	}
	offset, err := parseNumber(j["offset"])
	if err != nil {
		return zero, protocolError("invalid offset: " + err.Error())
	}
	minimum, err := parseNumber(j["minimum"])
	if err != nil {
		return zero, protocolError("invalid minimum: " + err.Error())
	}
	maximum, err := parseNumber(j["maximum"])
	if err != nil {
		return zero, protocolError("invalid maximum: " + err.Error())
	}
	startBit, err := parseNumber(j["startBit"])
	if err != nil {
		return zero, protocolError("invalid startBit: " + err.Error())
	}
	if startBit < 0 || startBit > 511 {
		return zero, protocolError(fmt.Sprintf("startBit %v out of range (0-511)", startBit))
	}
	length, err := parseNumber(j["length"])
	if err != nil {
		return zero, protocolError("invalid length: " + err.Error())
	}
	if length < 1 || length > 64 {
		return zero, protocolError(fmt.Sprintf("bit length %v out of range (1-64)", length))
	}

	var presence SignalPresence = AlwaysPresent{}
	if muxName := getString(j, "multiplexor"); muxName != "" {
		muxVal, err := parseNumber(j["multiplex_value"])
		if err != nil {
			return zero, protocolError("invalid multiplex_value: " + err.Error())
		}
		if muxVal < 0 || muxVal > math.MaxUint32 {
			return zero, protocolError(fmt.Sprintf("multiplex_value %v out of range (0-%d)", muxVal, uint32(math.MaxUint32)))
		}
		presence = Multiplexed{
			Multiplexor: SignalName(muxName),
			MuxValue:    MultiplexValue(muxVal),
		}
	}

	return DbcSignal{
		Name:      SignalName(getString(j, "name")),
		StartBit:  BitPosition(startBit),
		BitLength: BitLength(length),
		ByteOrder: bo,
		IsSigned:  getBool(j, "signed"),
		Factor:    ScaleFactor(factor),
		Offset:    ScaleOffset(offset),
		Minimum:   PhysicalValue(minimum),
		Maximum:   PhysicalValue(maximum),
		Unit:      Unit(getString(j, "unit")),
		Presence:  presence,
	}, nil
}
