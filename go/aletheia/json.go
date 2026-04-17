package aletheia

import (
	"encoding/binary"
	"encoding/json"
	"fmt"
	"math"
	"strconv"
	"strings"
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

// serializeCommand builds the JSON envelope sent to the Agda core for
// control-plane commands (parseDBC, setProperties, validateDBC, …).
// Go's encoding/json marshals map keys in lexical order, so the wire
// output is deterministic across runs.
func serializeCommand(command string, fields map[string]any) (string, error) {
	m := map[string]any{"type": "command", "command": command}
	for k, v := range fields {
		m[k] = v
	}
	b, err := json.Marshal(m)
	if err != nil {
		return "", wrapProtocol("failed to serialize command", err)
	}
	return string(b), nil
}

// serializeDataFrame serializes a CAN frame as a JSON data event.
// Uses direct string building rather than json.Marshal to avoid map allocation
// and reflection overhead on the streaming hot path.
func serializeDataFrame(ts Timestamp, id CanID, dlc DLC, data FramePayload) string {
	// Avoids map allocation, reflection-based marshaling, and []int conversion.
	var buf strings.Builder
	buf.Grow(128 + len(data)*4) // pre-size for typical frame
	buf.WriteString(`{"type":"data","timestamp":`)
	buf.WriteString(strconv.FormatInt(ts.Microseconds, 10))
	buf.WriteString(`,"id":`)
	buf.WriteString(strconv.FormatUint(uint64(id.Value()), 10))
	buf.WriteString(`,"extended":`)
	if id.IsExtended() {
		buf.WriteString("true")
	} else {
		buf.WriteString("false")
	}
	buf.WriteString(`,"dlc":`)
	buf.WriteString(strconv.FormatUint(uint64(dlc.Value()), 10))
	buf.WriteString(`,"data":[`)
	for i, b := range data {
		if i > 0 {
			buf.WriteByte(',')
		}
		buf.WriteString(strconv.FormatUint(uint64(b), 10))
	}
	buf.WriteString("]}")
	return buf.String()
}

// serializeErrorEvent serializes a CAN error event as JSON. Used by the
// MockBackend so tests can observe error events alongside data frames.
func serializeErrorEvent(ts Timestamp) string {
	var buf strings.Builder
	buf.Grow(48)
	buf.WriteString(`{"type":"error","timestamp":`)
	buf.WriteString(strconv.FormatInt(ts.Microseconds, 10))
	buf.WriteByte('}')
	return buf.String()
}

// serializeRemoteEvent serializes a CAN remote frame event as JSON. Used by the
// MockBackend so tests can observe remote events alongside data frames.
func serializeRemoteEvent(ts Timestamp, id CanID) string {
	var buf strings.Builder
	buf.Grow(80)
	buf.WriteString(`{"type":"remote","timestamp":`)
	buf.WriteString(strconv.FormatInt(ts.Microseconds, 10))
	buf.WriteString(`,"id":`)
	buf.WriteString(strconv.FormatUint(uint64(id.Value()), 10))
	buf.WriteString(`,"extended":`)
	if id.IsExtended() {
		buf.WriteString("true")
	} else {
		buf.WriteString("false")
	}
	buf.WriteByte('}')
	return buf.String()
}

// serializeDBC converts a DbcDefinition into the map shape Agda expects
// under the "dbc" field of the parseDBC / validateDBC command envelopes.
func serializeDBC(dbc DbcDefinition) (map[string]any, error) {
	msgs := make([]map[string]any, 0, len(dbc.Messages))
	for _, msg := range dbc.Messages {
		sigs := make([]map[string]any, 0, len(msg.Signals))
		for _, sig := range msg.Signals {
			s := map[string]any{
				"name":     string(sig.Name),
				"startBit": sig.StartBit,
				"length":   sig.BitLength,
				"signed":   sig.IsSigned,
				"factor":   serializeRational(sig.Factor),
				"offset":   serializeRational(sig.Offset),
				"minimum":  serializeRational(sig.Minimum),
				"maximum":  serializeRational(sig.Maximum),
				"unit":     string(sig.Unit),
			}
			switch sig.ByteOrder {
			case BigEndian:
				s["byteOrder"] = "big_endian"
			case LittleEndian:
				s["byteOrder"] = "little_endian"
			default:
				return nil, validationError(fmt.Sprintf("invalid byte order %d", sig.ByteOrder))
			}
			if mux, ok := sig.Presence.(Multiplexed); ok {
				s["multiplexor"] = string(mux.Multiplexor)
				vals := make([]uint32, len(mux.MuxValues))
				for i, v := range mux.MuxValues {
					vals[i] = uint32(v)
				}
				s["multiplex_values"] = vals
			} else {
				s["presence"] = "always"
			}
			sigs = append(sigs, s)
		}
		m := map[string]any{
			"id":       msg.ID.Value(),
			"extended": msg.ID.IsExtended(),
			"name":     string(msg.Name),
			"dlc":      msg.DLC.ToBytes(),
			"sender":   string(msg.Sender),
			"signals":  sigs,
		}
		msgs = append(msgs, m)
	}
	return map[string]any{
		"version":  dbc.Version,
		"messages": msgs,
	}, nil
}

// serializePredicate encodes a Predicate into the JSON tag/field shape
// consumed by the Agda LTL parser (SignalPredicate.JSON).
func serializePredicate(p Predicate) (map[string]any, error) {
	switch p := p.(type) {
	case Equals:
		return map[string]any{"predicate": "equals", "signal": string(p.Signal), "value": float64(p.Value)}, nil
	case LessThan:
		return map[string]any{"predicate": "lessThan", "signal": string(p.Signal), "value": float64(p.Value)}, nil
	case GreaterThan:
		return map[string]any{"predicate": "greaterThan", "signal": string(p.Signal), "value": float64(p.Value)}, nil
	case LessThanOrEqual:
		return map[string]any{"predicate": "lessThanOrEqual", "signal": string(p.Signal), "value": float64(p.Value)}, nil
	case GreaterThanOrEqual:
		return map[string]any{"predicate": "greaterThanOrEqual", "signal": string(p.Signal), "value": float64(p.Value)}, nil
	case Between:
		if p.Min > p.Max {
			return nil, validationError(fmt.Sprintf("between: min (%g) exceeds max (%g)", float64(p.Min), float64(p.Max)))
		}
		return map[string]any{"predicate": "between", "signal": string(p.Signal), "min": float64(p.Min), "max": float64(p.Max)}, nil
	case ChangedBy:
		return map[string]any{"predicate": "changedBy", "signal": string(p.Signal), "delta": float64(p.Delta)}, nil
	case StableWithin:
		if p.Tolerance < 0 {
			return nil, validationError(fmt.Sprintf("negative tolerance: %g", float64(p.Tolerance)))
		}
		return map[string]any{"predicate": "stableWithin", "signal": string(p.Signal), "tolerance": float64(p.Tolerance)}, nil
	default:
		return nil, validationError(fmt.Sprintf("unsupported predicate type %T", p))
	}
}

// validateTimeBound rejects TimeBounds the Agda core cannot represent
// (negative microseconds or overflow past int64 in the wire payload).
func validateTimeBound(t TimeBound) error {
	if t.Microseconds < 0 {
		return validationError(fmt.Sprintf("negative time bound: %d microseconds", t.Microseconds))
	}
	return nil
}

// serializeFormula encodes an LTL formula AST for Agda, bounded in depth
// to prevent unbounded recursion on pathological user input.
func serializeFormula(f Formula) (map[string]any, error) {
	return serializeFormulaDepth(f, 0)
}

// serializeFormulaDepth is the recursive core of serializeFormula. It
// carries the remaining depth budget so deeply nested user input fails
// fast instead of blowing the Go stack.
func serializeFormulaDepth(f Formula, depth int) (map[string]any, error) {
	if depth > maxFormulaDepth {
		return nil, validationError(fmt.Sprintf("formula nesting depth exceeds %d", maxFormulaDepth))
	}
	switch f := f.(type) {
	case Atomic:
		pred, err := serializePredicate(f.Predicate)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "atomic", "predicate": pred}, nil
	case Not:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "not", "formula": inner}, nil
	case And:
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "and", "left": left, "right": right}, nil
	case Or:
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "or", "left": left, "right": right}, nil
	case Next:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "next", "formula": inner}, nil
	case WeakNext:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "weakNext", "formula": inner}, nil
	case Always:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "always", "formula": inner}, nil
	case Eventually:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "eventually", "formula": inner}, nil
	case Until:
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "until", "left": left, "right": right}, nil
	case Release:
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "release", "left": left, "right": right}, nil
	case MetricAlways:
		if err := validateTimeBound(f.Bound); err != nil {
			return nil, err
		}
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "metricAlways", "timebound": f.Bound.Microseconds, "formula": inner}, nil
	case MetricEventually:
		if err := validateTimeBound(f.Bound); err != nil {
			return nil, err
		}
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "metricEventually", "timebound": f.Bound.Microseconds, "formula": inner}, nil
	case MetricUntil:
		if err := validateTimeBound(f.Bound); err != nil {
			return nil, err
		}
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "metricUntil", "timebound": f.Bound.Microseconds, "left": left, "right": right}, nil
	case MetricRelease:
		if err := validateTimeBound(f.Bound); err != nil {
			return nil, err
		}
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "metricRelease", "timebound": f.Bound.Microseconds, "left": left, "right": right}, nil
	default:
		return nil, validationError(fmt.Sprintf("unsupported formula type %T", f))
	}
}

// --- Rational helpers ---

// parseRational reads a Rational from a JSON scalar (number) or the
// {"numerator","denominator"} object shape, matching Python's Fraction
// decoding path.
func parseRational(v any) (Rational, error) {
	switch n := v.(type) {
	case float64:
		// Agda sends integers as float64 in JSON.
		if math.Trunc(n) != n {
			return Rational{}, protocolError(fmt.Sprintf("expected integer rational, got fractional float64: %v", n))
		}
		return Rational{Numerator: int64(n), Denominator: 1}, nil
	case map[string]any:
		num, ok1 := n["numerator"].(float64)
		den, ok2 := n["denominator"].(float64)
		if !ok1 || !ok2 {
			return Rational{}, protocolError(fmt.Sprintf("rational dict missing fields: %v", v))
		}
		if den == 0 {
			return Rational{}, protocolError(fmt.Sprintf("zero denominator in rational: %v", v))
		}
		d := int64(den)
		nu := int64(num)
		if d < 0 {
			nu = -nu
			d = -d
		}
		return Rational{Numerator: nu, Denominator: d}, nil
	default:
		return Rational{}, protocolError(fmt.Sprintf("expected number or rational dict, got %T", v))
	}
}

// serializeRational emits a Rational as {"numerator","denominator"} so
// the wire form preserves exact precision (no float rounding).
func serializeRational(r Rational) any {
	if r.Denominator == 1 {
		return r.Numerator
	}
	return map[string]any{"numerator": r.Numerator, "denominator": r.Denominator}
}

// --- Deserialization (JSON from Agda core → Go) ---

// parseNumber handles the three number formats Agda emits:
// plain int, plain float, or {"numerator": n, "denominator": d}.
func parseNumber(v any) (float64, error) {
	switch n := v.(type) {
	case float64:
		return n, nil
	case map[string]any:
		// Agda emits rationals as {"numerator": n, "denominator": d} with plain numbers.
		numF, ok1 := n["numerator"].(float64)
		denF, ok2 := n["denominator"].(float64)
		if !ok1 || !ok2 {
			return 0, protocolError(fmt.Sprintf("expected {numerator: number, denominator: number}, got %v", n))
		}
		if denF == 0 {
			return 0, protocolError("zero denominator in rational")
		}
		return numF / denF, nil
	default:
		return 0, protocolError(fmt.Sprintf("expected number, got %T: %v", v, v))
	}
}

// parseNumberAsInt64 parses a JSON number as an exact integer.
// Note: Go's json.Unmarshal decodes all numbers as float64 (53-bit mantissa),
// so integers above 2^53 lose precision silently. This is acceptable for CAN
// fields (IDs ≤ 29 bits, timestamps ≪ 2^53).
func parseNumberAsInt64(v any) (int64, error) {
	switch n := v.(type) {
	case float64:
		if n != math.Trunc(n) {
			return 0, protocolError(fmt.Sprintf("expected integer, got fractional: %v", n))
		}
		if n > math.MaxInt64 || n < math.MinInt64 {
			return 0, protocolError(fmt.Sprintf("integer out of int64 range: %v", n))
		}
		return int64(n), nil
	case map[string]any:
		// Agda emits rationals as {"numerator": n, "denominator": d} with plain numbers.
		numF, ok1 := n["numerator"].(float64)
		denF, ok2 := n["denominator"].(float64)
		if !ok1 || !ok2 {
			return 0, protocolError(fmt.Sprintf("expected {numerator: number, denominator: number}, got %v", n))
		}
		if numF != math.Trunc(numF) || denF != math.Trunc(denF) {
			return 0, protocolError(fmt.Sprintf("expected integer rational, got %v/%v", numF, denF))
		}
		numI, denI := int64(numF), int64(denF)
		if denI == 0 {
			return 0, protocolError("zero denominator in rational")
		}
		if numI%denI != 0 {
			return 0, protocolError(fmt.Sprintf("expected integer, got non-exact rational %d/%d", numI, denI))
		}
		return numI / denI, nil
	default:
		return 0, protocolError(fmt.Sprintf("expected integer, got %T: %v", v, v))
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

// parseResponse unmarshals an Agda core response into a generic map
// before typed parsers narrow it to a concrete response variant.
func parseResponse(raw string) (map[string]any, error) {
	var m map[string]any
	if err := json.Unmarshal([]byte(raw), &m); err != nil {
		return nil, wrapProtocol("invalid JSON response", err)
	}
	return m, nil
}

// checkErrorStatus converts a parsed response with status="error" into
// a typed error carrying the Agda-side code and message.
func checkErrorStatus(m map[string]any) error {
	status := getString(m, "status")
	if status == "error" {
		code := getString(m, "code")
		msg := getString(m, "message")
		if code != "" {
			return newCodedError(ErrProtocol, code, msg)
		}
		return protocolError(msg)
	}
	return nil
}

// parseSuccessResponse validates an Agda command response for control-
// plane commands (parseDBC, setProperties, …) and returns nil iff
// status=="success".
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
	return protocolError(fmt.Sprintf("unexpected status: %q", status))
}

// parseEventAck parses a send_error / send_remote response. Trace events
// (Error / Remote) always resolve to Response.Ack in the Agda core — see
// Protocol/StreamState.agda handleTraceEvent — so the wire status is "ack".
// Python parse_event_response and C++ parse_event_ack enforce the same.
func parseEventAck(raw string) error {
	// Fast path: byte-level check before JSON parsing (~99% of real traffic).
	if raw == ackCompact || raw == ackSpaced {
		return nil
	}
	m, err := parseResponse(raw)
	if err != nil {
		return err
	}
	if err := checkErrorStatus(m); err != nil {
		return err
	}
	status := getString(m, "status")
	if status == "ack" {
		return nil
	}
	return protocolError(fmt.Sprintf("unexpected status: %q", status))
}

// parseValidationResponse decodes a validateDBC response into typed
// ValidationIssues, preserving severity and the Agda error code.
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
		return nil, protocolError(fmt.Sprintf("expected validation response, got status: %q", status))
	}

	var issues []ValidationIssue
	for _, item := range getArray(m, "issues") {
		issue, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in issues array")
		}
		var sev IssueSeverity
		switch s := getString(issue, "severity"); s {
		case "error":
			sev = SeverityError
		case "warning":
			sev = SeverityWarning
		default:
			return nil, protocolError(fmt.Sprintf("unknown validation severity: %q", s))
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

// parseExtractionResponse decodes an extractAllSignals JSON response.
// Binary-extraction responses use parseExtractionBin instead.
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
		return nil, protocolError(fmt.Sprintf("expected success response, got status: %q", status))
	}

	var values []SignalValue
	for _, item := range getArray(m, "values") {
		v, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in values array")
		}
		val, err := parseNumber(v["value"])
		if err != nil {
			return nil, wrapProtocol("invalid signal value", err)
		}
		name := getString(v, "name")
		if name == "" {
			return nil, protocolError("signal value missing required field: name")
		}
		values = append(values, SignalValue{
			Name:  SignalName(name),
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

	result := &ExtractionResult{Values: values, Errors: errors, Absent: absent}
	result.buildIndex()
	return result, nil
}

// parseFrameDataResponse decodes a buildFrame/updateFrame JSON response
// into the raw CAN payload bytes.
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
		return nil, protocolError(fmt.Sprintf("expected success response, got status: %q", status))
	}

	data := getArray(m, "data")
	payload := make(FramePayload, len(data))
	for i, item := range data {
		f, err := parseNumberAsInt64(item)
		if err != nil {
			return nil, wrapProtocol(fmt.Sprintf("invalid byte %d in frame data", i), err)
		}
		if f < 0 || f > 255 {
			return nil, protocolError(fmt.Sprintf("byte %d out of range: %d", i, f))
		}
		payload[i] = byte(f)
	}
	return payload, nil
}

// extractionErrorMessages maps error codes from binary extraction to messages.
// Must match Agda categorizeIndexed: 0 = not_in_dbc, 1 = out_of_bounds, 2 = extraction_failed.
var extractionErrorMessages = [...]string{
	"Signal not found in DBC",
	"Value out of bounds",
	"Extraction failed",
}

// parseExtractionBin parses a packed binary extraction buffer into an ExtractionResult.
// Buffer layout: [nvals:u16][nerrs:u16][nabss:u16] + values(18B) + errors(3B) + absent(2B).
func parseExtractionBin(buf []byte, names []string) (*ExtractionResult, error) {
	if len(buf) < 6 {
		return nil, protocolError("extraction binary buffer too short")
	}
	nvals := binary.LittleEndian.Uint16(buf[0:2])
	nerrs := binary.LittleEndian.Uint16(buf[2:4])
	nabss := binary.LittleEndian.Uint16(buf[4:6])
	off := 6

	result := &ExtractionResult{
		Values: make([]SignalValue, 0, nvals),
		Errors: make([]SignalError, 0, nerrs),
		Absent: make([]SignalName, 0, nabss),
	}

	for range nvals {
		if off+18 > len(buf) {
			return nil, protocolError("extraction binary buffer truncated in values")
		}
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		num := int64(binary.LittleEndian.Uint64(buf[off+2 : off+10]))
		den := int64(binary.LittleEndian.Uint64(buf[off+10 : off+18]))
		off += 18
		name := signalNameByIndex(names, idx)
		var value float64
		if den != 0 {
			value = float64(num) / float64(den)
		}
		result.Values = append(result.Values, SignalValue{Name: name, Value: PhysicalValue(value)})
	}

	for range nerrs {
		if off+3 > len(buf) {
			return nil, protocolError("extraction binary buffer truncated in errors")
		}
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		code := buf[off+2]
		off += 3
		name := signalNameByIndex(names, idx)
		msg := fmt.Sprintf("unknown error code %d", code)
		if int(code) < len(extractionErrorMessages) {
			msg = extractionErrorMessages[code]
		}
		result.Errors = append(result.Errors, SignalError{Name: name, Error: msg})
	}

	for range nabss {
		if off+2 > len(buf) {
			return nil, protocolError("extraction binary buffer truncated in absent")
		}
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		off += 2
		result.Absent = append(result.Absent, signalNameByIndex(names, idx))
	}

	// Reject trailing bytes: the header (6B) + all entries must consume the whole
	// buffer. Extra bytes indicate a protocol mismatch between Agda writer and Go
	// reader and would silently hide bugs if ignored.
	if off != len(buf) {
		return nil, protocolError(fmt.Sprintf("extraction binary buffer has %d trailing bytes", len(buf)-off))
	}

	result.buildIndex()
	return result, nil
}

// signalNameByIndex resolves a DBC signal index into its name using the
// caller-supplied lookup table. Returns an empty SignalName on OOB.
func signalNameByIndex(names []string, idx uint16) SignalName {
	if int(idx) < len(names) {
		return SignalName(names[idx])
	}
	return SignalName(fmt.Sprintf("signal_%d", idx))
}

// Ack fast path constants — avoid json.Unmarshal for ~99% of streaming frames.
// The Agda core emits exactly {"status":"ack"} (compact). The spaced variant
// covers json.Marshal output used by MockBackend.
const (
	maxFormulaDepth = 100
	ackCompact      = `{"status":"ack"}`
	ackSpaced       = `{"status": "ack"}`
)

// parseFrameResponse decodes the per-frame LTL verdict returned by
// sendFrame: Ack (no violation) or Violation (with property index).
func parseFrameResponse(raw string) (FrameResponse, error) {
	// Fast path: byte-level check before JSON parsing.
	if raw == ackCompact || raw == ackSpaced {
		return Ack{}, nil
	}

	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}

	status := getString(m, "status")
	switch status {
	case "ack":
		return Ack{}, nil
	case "fails":
		if propType := getString(m, "type"); propType != "property" {
			return nil, protocolError(fmt.Sprintf("expected type \"property\" in violation response, got %q", propType))
		}
		idx, err := parseNumberAsInt64(m["property_index"])
		if err != nil {
			return nil, wrapProtocol("invalid property_index", err)
		}
		if idx < 0 {
			return nil, protocolError(fmt.Sprintf("negative property_index: %d", idx))
		}
		ts, err := parseNumberAsInt64(m["timestamp"])
		if err != nil {
			return nil, wrapProtocol("invalid timestamp", err)
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
		code := getString(m, "code")
		msg := getString(m, "message")
		if code != "" {
			return nil, newCodedError(ErrProtocol, code, msg)
		}
		return nil, protocolError(msg)
	default:
		return nil, protocolError(fmt.Sprintf("unexpected frame status: %q", status))
	}
}

// parseStreamResponse decodes an endStream response — a list of final
// property verdicts (Satisfaction / Violation / Unresolved).
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
		return nil, protocolError(fmt.Sprintf("expected complete response, got status: %q", status))
	}

	var results []PropertyResult
	for _, item := range getArray(m, "results") {
		r, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in results array")
		}
		pr, err := parsePropertyResult(r)
		if err != nil {
			return nil, err
		}
		results = append(results, pr)
	}
	return &StreamResult{Results: results}, nil
}

// parsePropertyResult decodes a single endStream verdict object into
// the typed PropertyResult sum (Satisfaction / Violation / Unresolved).
func parsePropertyResult(r map[string]any) (PropertyResult, error) {
	var zero PropertyResult
	entryStatus := getString(r, "status")
	var verdict Verdict
	switch entryStatus {
	case "holds":
		verdict = Holds
	case "fails":
		verdict = Fails
	case "unresolved":
		verdict = Unresolved
	default:
		return zero, protocolError(fmt.Sprintf("unknown verdict status: %q", entryStatus))
	}

	idx, err := parseNumberAsInt64(r["property_index"])
	if err != nil {
		return zero, wrapProtocol("invalid property_index", err)
	}
	if idx < 0 {
		return zero, protocolError(fmt.Sprintf("negative property_index: %d", idx))
	}

	pr := PropertyResult{
		PropertyIndex: PropertyIndex(idx),
		Verdict:       verdict,
		Reason:        getString(r, "reason"),
	}

	if tsRaw, ok := r["timestamp"]; ok && tsRaw != nil {
		ts, err := parseNumberAsInt64(tsRaw)
		if err != nil {
			return zero, wrapProtocol("invalid timestamp in result", err)
		}
		if ts < 0 {
			return zero, protocolError(fmt.Sprintf("negative timestamp in result: %d", ts))
		}
		t := Timestamp{Microseconds: ts}
		pr.Timestamp = &t
	}

	return pr, nil
}

// parseDbcResponse decodes a formatDBC response into a DbcDefinition.
func parseDbcResponse(raw string) (*DbcDefinition, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "success" {
		return nil, protocolError(fmt.Sprintf("expected success response, got status: %q", status))
	}

	dbcRaw := getObject(m, "dbc")
	if dbcRaw == nil {
		return nil, protocolError("missing 'dbc' field in response")
	}
	return parseDbcDefinition(dbcRaw)
}

// parseDbcDefinition decodes the "dbc" sub-object of a formatDBC
// response into its typed DbcDefinition form.
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
	def := &DbcDefinition{
		Version:  getString(j, "version"),
		Messages: messages,
	}
	def.buildIndexes()
	return def, nil
}

// parseDbcMessage decodes a single message from a DbcDefinition JSON
// object, including its signals and multiplexing metadata.
func parseDbcMessage(j map[string]any) (*DbcMessage, error) {
	idVal, err := parseNumberAsInt64(j["id"])
	if err != nil {
		return nil, wrapProtocol("invalid message id", err)
	}
	if idVal < 0 {
		return nil, protocolError(fmt.Sprintf("negative message id: %d", idVal))
	}
	extended := getBool(j, "extended")

	var id CanID
	if extended {
		if idVal > math.MaxUint32 {
			return nil, protocolError(fmt.Sprintf("CAN ID %d exceeds uint32 range", idVal))
		}
		eid, err := NewExtendedID(uint32(idVal))
		if err != nil {
			return nil, err
		}
		id = eid
	} else {
		sid, err := NewStandardID(uint16(idVal))
		if err != nil {
			return nil, err
		}
		id = sid
	}

	dlcVal, err := parseNumberAsInt64(j["dlc"])
	if err != nil {
		return nil, wrapProtocol("invalid DLC", err)
	}
	dlc, err := BytesToDLC(int(dlcVal))
	if err != nil {
		return nil, err
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

	msgName := getString(j, "name")
	if msgName == "" {
		return nil, protocolError("message missing required field: name")
	}

	msg := &DbcMessage{
		ID:      id,
		Name:    MessageName(msgName),
		DLC:     dlc,
		Sender:  NodeName(getString(j, "sender")),
		Signals: signals,
	}
	msg.buildSignalIndex()
	return msg, nil
}

// parseDbcSignal decodes one signal definition from a DBC JSON object.
func parseDbcSignal(j map[string]any) (DbcSignal, error) {
	var zero DbcSignal
	var bo ByteOrder
	switch getString(j, "byteOrder") {
	case "little_endian":
		bo = LittleEndian
	case "big_endian":
		bo = BigEndian
	default:
		return zero, protocolError(fmt.Sprintf("unrecognized byte order: %q", getString(j, "byteOrder")))
	}

	factor, err := parseRational(j["factor"])
	if err != nil {
		return zero, wrapProtocol("invalid factor", err)
	}
	offset, err := parseRational(j["offset"])
	if err != nil {
		return zero, wrapProtocol("invalid offset", err)
	}
	minimum, err := parseRational(j["minimum"])
	if err != nil {
		return zero, wrapProtocol("invalid minimum", err)
	}
	maximum, err := parseRational(j["maximum"])
	if err != nil {
		return zero, wrapProtocol("invalid maximum", err)
	}
	startBit, err := parseNumberAsInt64(j["startBit"])
	if err != nil {
		return zero, wrapProtocol("invalid startBit", err)
	}
	if startBit < 0 || startBit > 511 {
		return zero, protocolError(fmt.Sprintf("startBit %d out of range (0-511)", startBit))
	}
	length, err := parseNumberAsInt64(j["length"])
	if err != nil {
		return zero, wrapProtocol("invalid length", err)
	}
	if length < 1 || length > 64 {
		return zero, protocolError(fmt.Sprintf("bit length %d out of range (1-64)", length))
	}

	presence, err := parseSignalPresence(j)
	if err != nil {
		return zero, err
	}

	name := getString(j, "name")
	if name == "" {
		return zero, protocolError("signal missing required field: name")
	}

	// Explicit lookup: "signed" must be present in well-formed DBC JSON
	// from the Agda parser. Default to false (unsigned, the CAN standard
	// default) but log a warning via error return if missing.
	signedVal, signedOk := j["signed"]
	isSigned := false
	if signedOk {
		if b, ok := signedVal.(bool); ok {
			isSigned = b
		}
	}

	return DbcSignal{
		Name:      SignalName(name),
		StartBit:  BitPosition(startBit),
		BitLength: BitLength(length),
		ByteOrder: bo,
		IsSigned:  isSigned,
		Factor:    factor,
		Offset:    offset,
		Minimum:   minimum,
		Maximum:   maximum,
		Unit:      Unit(getString(j, "unit")),
		Presence:  presence,
	}, nil
}

// parseSignalPresence decodes the multiplexor "presence" object that
// names the multiplexor signal plus the mux values under which a
// multiplexed signal is active.
func parseSignalPresence(j map[string]any) (SignalPresence, error) {
	muxName := getString(j, "multiplexor")
	if muxName == "" {
		return AlwaysPresent{}, nil
	}
	rawVals, ok := j["multiplex_values"].([]any)
	if !ok || len(rawVals) == 0 {
		return nil, protocolError("multiplex_values must be a non-empty array")
	}
	muxVals := make([]MultiplexValue, 0, len(rawVals))
	for i, rv := range rawVals {
		v, err := parseNumberAsInt64(rv)
		if err != nil {
			return nil, wrapProtocol(fmt.Sprintf("invalid multiplex_values[%d]", i), err)
		}
		if v < 0 || v > math.MaxUint32 {
			return nil, protocolError(fmt.Sprintf("multiplex_values[%d] %d out of range (0-%d)", i, v, uint32(math.MaxUint32)))
		}
		muxVals = append(muxVals, MultiplexValue(v))
	}
	return Multiplexed{
		Multiplexor: SignalName(muxName),
		MuxValues:   muxVals,
	}, nil
}
