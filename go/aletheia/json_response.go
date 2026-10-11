// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"strconv"
	"strings"
	"unicode/utf8"
)

// --- Deserialization: the kernel's JSON to Go ---

// intParse classifies the outcome of decoding a JSON number as an int64.
type intParse int

const (
	intParseOK         intParse = iota // an exact int64
	intParseNotNumber                  // not a JSON number at all
	intParseFractional                 // numeric, but has a fractional part
	intParseOverflow                   // integer-valued, but outside int64
)

// decodeJSONInt reads a wire number as an exact int64. There is no float64
// arm on purpose: a value that is not a json.Number did not come off the wire
// through parseResponse, and taking it would put every integer through a
// float's 53 bits of mantissa.
func decodeJSONInt(v any) (int64, intParse) {
	switch n := v.(type) {
	case json.Number:
		i, err := strconv.ParseInt(n.String(), 10, 64)
		if err == nil {
			return i, intParseOK
		}
		// A fractional, exponent or out-of-range literal is refused. The kernel
		// writes plain integers, which the other bindings' readers also require,
		// so nothing is lost by refusing the rest.
		if errors.Is(err, strconv.ErrRange) {
			return 0, intParseOverflow
		}
		return 0, intParseFractional
	default:
		return 0, intParseNotNumber
	}
}

// narrow is v as a T, and whether T holds v exactly: a value past either end
// of T comes back changed by the conversion, so the round trip refuses it
// without a bound written by hand.
func narrow[T ~uint8 | ~uint16 | ~uint32 | ~int32](v int64) (T, bool) {
	t := T(v)
	return t, int64(t) == v
}

// parseNumberAsInt64 reads an exact int64 from a wire number, or from a
// rational that divides evenly.
func parseNumberAsInt64(v any) (int64, error) {
	switch n := v.(type) {
	case json.Number:
		i, cls := decodeJSONInt(v)
		// The value is a number here, so only the fractional and the
		// out-of-range answers can come back.
		switch cls {
		case intParseFractional:
			return 0, protocolError(fmt.Sprintf("expected integer, got fractional: %v", v))
		case intParseOverflow:
			return 0, protocolError(fmt.Sprintf("integer out of int64 range: %v", v))
		}
		return i, nil
	case map[string]any:
		num, den, err := rationalParts(n)
		if err != nil {
			return 0, err
		}
		if num%den != 0 {
			return 0, protocolError(fmt.Sprintf("expected integer, got non-exact rational %d/%d", num, den))
		}
		return num / den, nil
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

// parseResponse reads a kernel response into a generic map, which the typed
// decoders below narrow.
//
// Numbers arrive as decimal strings rather than float64, so a numerator or
// denominator above two to the fifty-third survives; the three numeric helpers
// read them exactly. A decoder accepts trailing bytes where json.Unmarshal
// refuses them, so the refusal is made here: a response is one JSON value.
func parseResponse(raw string) (map[string]any, error) {
	dec := json.NewDecoder(strings.NewReader(raw))
	dec.UseNumber()
	var m map[string]any
	if err := dec.Decode(&m); err != nil {
		return nil, wrapProtocolError("invalid JSON response", err)
	}
	if err := dec.Decode(new(json.RawMessage)); err == nil {
		return nil, protocolError("unexpected trailing data after JSON response")
	} else if !errors.Is(err, io.EOF) {
		return nil, wrapProtocolError("invalid trailing data after JSON response", err)
	}
	return m, nil
}

// decodeResponse reads a response, lifts an error envelope into its typed
// error, and holds the status to the one the caller expects. Every typed
// decoder below opens with it, so a response that is malformed, an error, or
// simply not the answer to the command asked is refused in one place.
func decodeResponse(raw, wantStatus string) (map[string]any, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	if status := getString(m, "status"); status != wantStatus {
		return nil, protocolError(fmt.Sprintf("expected %s response, got status: %q", wantStatus, status))
	}
	return m, nil
}

// requireString reads a field that must be there. An error response carries
// its code and its message, so a default in place of either would hide drift
// between the binding and the kernel rather than report it. The Python decoder
// requires the same two in build_error_response.
func requireString(m map[string]any, key string) (string, error) {
	v, ok := m[key]
	if !ok {
		return "", protocolError(fmt.Sprintf(
			"Error response missing or non-string '%s' field; got <absent>", key))
	}
	s, ok := v.(string)
	if !ok {
		return "", protocolError(fmt.Sprintf(
			"Error response missing or non-string '%s' field; got %T", key, v))
	}
	return s, nil
}

// The three lifts below turn a coded error response into the typed error a
// caller can match on, and each answers nil when its payload is incomplete, so
// the caller falls back to the generic coded error and the decode never fails
// harder than it would have. C++ and Python degrade the same way.

// inputBoundExceededFromResponse lifts a bound refusal, whichever bound the
// kernel crossed. The typed error keeps the kind, the observed size, the
// limit, the field the refusal names, if it names one, and the kernel's
// message, which is its text. A field that is not a string degrades the lift
// as a malformed number does.
func inputBoundExceededFromResponse(code, msg string, m map[string]any) *InputBoundExceededError {
	if code != CodeInputBoundExceeded {
		return nil
	}
	kind, ok := m["bound_kind"].(string)
	if !ok {
		return nil
	}
	observed, ok := jsonNumberToUint64(m["observed"])
	if !ok {
		return nil
	}
	limit, ok := jsonNumberToUint64(m["limit"])
	if !ok {
		return nil
	}
	var field string
	if raw, named := m["field"]; named {
		if field, ok = raw.(string); !ok {
			return nil
		}
	}
	return newInputBoundExceededError(kind, observed, limit, code, field, msg)
}

// jsonNumberToUint64 reads a wire number as an exact uint64, refusing a
// negative, a fractional, an exponent form and anything too large.
func jsonNumberToUint64(v any) (uint64, bool) {
	switch n := v.(type) {
	case json.Number:
		i, err := strconv.ParseUint(n.String(), 10, 64)
		if err != nil {
			return 0, false
		}
		return i, true
	default:
		return 0, false
	}
}

// validationFailedFromResponse lifts a refusal of a DBC that failed
// validation. The issues have the element shape of a validation response, so
// parseIssueArray decodes them; their presence is checked first, since a
// missing key would otherwise read as an empty array. The wire message is
// carried through, so the rendered error is what the generic one rendered.
func validationFailedFromResponse(code, msg string, m map[string]any) *ValidationFailedError {
	if code != CodeHandlerValidationFailed {
		return nil
	}
	hasErrors, ok := m["has_errors"].(bool)
	if !ok {
		return nil
	}
	if _, ok := m["issues"].([]any); !ok {
		return nil
	}
	issues, err := parseIssueArray(m, "issues")
	if err != nil {
		return nil
	}
	return newValidationFailedError(issues, hasErrors, code, msg)
}

// textRoundtripFailedFromResponse lifts a refusal of a DBC whose text does not
// re-parse, carrying the same payload as the validation refusal above.
func textRoundtripFailedFromResponse(code, msg string, m map[string]any) *TextRoundTripFailedError {
	if code != CodeHandlerTextRoundtripFailed {
		return nil
	}
	hasErrors, ok := m["has_errors"].(bool)
	if !ok {
		return nil
	}
	if _, ok := m["issues"].([]any); !ok {
		return nil
	}
	issues, err := parseIssueArray(m, "issues")
	if err != nil {
		return nil
	}
	return newTextRoundTripFailedError(issues, hasErrors, code, msg)
}

// checkErrorStatus turns an error response into a typed error carrying the
// kernel's code and message, both of which must be strings. Where the response
// also carries a structured payload, one of the lifts above gives the caller a
// type to match on instead of the generic coded error.
func checkErrorStatus(m map[string]any) error {
	status := getString(m, "status")
	if status != "error" {
		return nil
	}
	code, err := requireString(m, "code")
	if err != nil {
		return err
	}
	msg, err := requireString(m, "message")
	if err != nil {
		return err
	}
	if bex := inputBoundExceededFromResponse(code, msg, m); bex != nil {
		return bex
	}
	if vfe := validationFailedFromResponse(code, msg, m); vfe != nil {
		return vfe
	}
	if trte := textRoundtripFailedFromResponse(code, msg, m); trte != nil {
		return trte
	}
	return newCodedError(ErrProtocol, code, msg)
}

// parseSuccessResponse is the answer to a control-plane command that carries
// nothing but its success.
func parseSuccessResponse(raw string) error {
	_, err := decodeResponse(raw, "success")
	return err
}

// parseEventAck reads the answer to an error or remote event. handleTraceEvent
// in Protocol/StreamState.agda resolves both to an acknowledgement, so that is
// the only status either can carry, and the Python and C++ decoders hold their
// events to the same one.
func parseEventAck(raw string) error {
	// Almost every response is one of the two spellings of an acknowledgement,
	// and comparing bytes is cheaper than parsing them.
	if raw == ackCompact || raw == ackSpaced {
		return nil
	}
	_, err := decodeResponse(raw, "ack")
	return err
}

// parseIssueArray decodes the validation issues under a key, for the
// validation response and for the warnings of a parsed DBC. The result is
// empty rather than nil, so encoding it again writes an empty array and not a
// null, which is what the Python decoder answers.
func parseIssueArray(m map[string]any, key string) ([]ValidationIssue, error) {
	issues := []ValidationIssue{}
	for _, item := range getArray(m, key) {
		issue, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError(fmt.Sprintf("expected object in %s array", key))
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
	return issues, nil
}

// parseValidationResponse decodes a validateDBC response into typed
// ValidationIssues, preserving severity and the Agda error code.
func parseValidationResponse(raw string) (*ValidationResult, error) {
	m, err := decodeResponse(raw, "validation")
	if err != nil {
		return nil, err
	}
	issues, err := parseIssueArray(m, "issues")
	if err != nil {
		return nil, err
	}
	return &ValidationResult{
		HasErrors: getBool(m, "has_errors"),
		Issues:    issues,
	}, nil
}

// parseExtractionResponse decodes an extractAllSignals JSON response.
// Binary-extraction responses use parseExtractionBin instead.
func parseExtractionResponse(raw string) (*ExtractionResult, error) {
	m, err := decodeResponse(raw, "success")
	if err != nil {
		return nil, err
	}

	var values []SignalValue
	for _, item := range getArray(m, "values") {
		v, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in values array")
		}
		r, err := parseRational(v["value"])
		if err != nil {
			return nil, wrapProtocolError("invalid signal value", err)
		}
		name := getString(v, "name")
		if name == "" {
			return nil, protocolError("signal value missing required field: name")
		}
		values = append(values, SignalValue{
			Name:  SignalName(name),
			Value: r,
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

// parseFrameDataResponse reads a payload out of a JSON response. Only the mock
// backend answers this way; the library returns the bytes themselves.
func parseFrameDataResponse(raw string) (FramePayload, error) {
	m, err := decodeResponse(raw, "success")
	if err != nil {
		return nil, err
	}

	data := getArray(m, "data")
	payload := make(FramePayload, len(data))
	for i, item := range data {
		f, err := parseNumberAsInt64(item)
		if err != nil {
			return nil, wrapProtocolError(fmt.Sprintf("invalid byte %d in frame data", i), err)
		}
		b, ok := narrow[byte](f)
		if !ok {
			return nil, protocolError(fmt.Sprintf("byte %d out of range: %d", i, f))
		}
		payload[i] = b
	}
	return payload, nil
}

// parseExtractionBin parses a packed binary extraction buffer into an ExtractionResult.
//
// Buffer layout (canonical wire doc: the processExtractBin header comment in
// src/Aletheia/Main/Binary.agda):
//
//	Header:  [nvals:u16][nerrs:u16][nabss:u16][reasonBytes:u32]  (10 bytes)
//	Values:  nvals × (idx:u16, num:i64, den:i64)                 (18 bytes each)
//	Errors:  nerrs × (idx:u16, code:u8)                          (3 bytes each)
//	Offsets: (nerrs+1) x u32, cumulative byte offsets into Reasons;
//	         off[0] = 0, monotone non-decreasing, off[nerrs] = reasonBytes.
//	Reasons: reasonBytes of UTF-8; error i's reason = bytes [off[i], off[i+1]).
//	Absent:  nabss × (idx:u16)                                   (2 bytes each)
//
// Each reason is the kernel's own string, byte for byte what the JSON path
// carries for the same error. The one-byte code beside it, whose table is
// extractionErrorCodeToℕ in Aletheia.CAN.BatchExtraction, is carried for a
// machine to read but is not put on the result: the JSON path has no such
// field, and the two paths present the same surface. A code outside the table
// is not refused, the reason being what the caller reads.
func parseExtractionBin(buf []byte, names []string) (*ExtractionResult, error) {
	// The header, and the offsets table's one entry that a buffer without
	// errors still carries, make the smallest buffer there is.
	const headerSize = 10
	if len(buf) < headerSize+4 {
		return nil, protocolError("extraction binary buffer too short")
	}
	nvals := int(binary.LittleEndian.Uint16(buf[0:2]))
	nerrs := int(binary.LittleEndian.Uint16(buf[2:4]))
	nabss := int(binary.LittleEndian.Uint16(buf[4:6]))
	reasonBytes := int(binary.LittleEndian.Uint32(buf[6:10]))

	// The size must be exact, short and long alike: either means the writer and
	// this reader disagree about the layout.
	want := headerSize + 18*nvals + 3*nerrs + 4*(nerrs+1) + reasonBytes + 2*nabss
	if len(buf) != want {
		return nil, protocolError(fmt.Sprintf("extraction binary buffer size mismatch: got %d bytes, want %d", len(buf), want))
	}
	off := headerSize

	result := &ExtractionResult{
		Values: make([]SignalValue, 0, nvals),
		Errors: make([]SignalError, 0, nerrs),
		Absent: make([]SignalName, 0, nabss),
	}

	for range nvals {
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		num := int64(binary.LittleEndian.Uint64(buf[off+2 : off+10]))
		den := int64(binary.LittleEndian.Uint64(buf[off+10 : off+18]))
		off += 18
		name := signalNameByIndex(names, idx)
		// The rational is the kernel's own, never rounded. A denominator of
		// zero or less is a corrupt buffer rather than a value, and the JSON
		// path refuses it too.
		if den <= 0 {
			return nil, protocolError(fmt.Sprintf("non-positive denominator %d for extracted signal %q (index %d)", den, name, idx))
		}
		result.Values = append(result.Values, SignalValue{Name: name, Value: Rational{Numerator: num, Denominator: den}})
	}

	// Each error carries its signal index and its code, the code carried but
	// not surfaced; the reasons live in the blob after the offsets table,
	// which is read where it lies. The table is always there, its one entry
	// zero when no error is, and all three of its invariants hold before
	// anything is sliced out of the blob.
	errsAt := off
	offsetsAt := errsAt + 3*nerrs
	offset := func(i int) int { return int(binary.LittleEndian.Uint32(buf[offsetsAt+4*i:])) }
	if first := offset(0); first != 0 {
		return nil, protocolError(fmt.Sprintf("extraction binary reason offsets must start at 0, got %d", first))
	}
	for i := 1; i <= nerrs; i++ {
		if offset(i) < offset(i-1) {
			return nil, protocolError(fmt.Sprintf("extraction binary reason offsets not monotone: offset %d is %d after %d", i, offset(i), offset(i-1)))
		}
	}
	if last := offset(nerrs); last != reasonBytes {
		return nil, protocolError(fmt.Sprintf("extraction binary reason offsets end at %d, want reasonBytes %d", last, reasonBytes))
	}
	reasonsAt := offsetsAt + 4*(nerrs+1)
	reasons := buf[reasonsAt : reasonsAt+reasonBytes]
	for i := range nerrs {
		reason := reasons[offset(i):offset(i+1)]
		if !utf8.Valid(reason) {
			return nil, protocolError(fmt.Sprintf("extraction binary reason %d is not valid UTF-8", i))
		}
		idx := binary.LittleEndian.Uint16(buf[errsAt+3*i:])
		result.Errors = append(result.Errors, SignalError{Name: signalNameByIndex(names, idx), Error: string(reason)})
	}
	off = reasonsAt + reasonBytes

	for range nabss {
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		off += 2
		result.Absent = append(result.Absent, signalNameByIndex(names, idx))
	}

	result.buildIndex()
	return result, nil
}

// signalNameByIndex is the name at an index of the caller's table. An index
// past the table answers a placeholder naming the number, which is for reading
// in a diagnostic: the kernel indexes the table it was given, so reaching it
// means the binding lost track of the names.
func signalNameByIndex(names []string, idx uint16) SignalName {
	if int(idx) < len(names) {
		return SignalName(names[idx])
	}
	return SignalName(fmt.Sprintf("signal_%d", idx))
}

// maxFormulaDepth bounds how deep a formula may nest.
const maxFormulaDepth = 100

// The two spellings of an acknowledgement: the kernel writes the compact one
// and the mock backend the spaced one.
const (
	ackCompact = `{"status":"ack"}`
	ackSpaced  = `{"status": "ack"}`
)

// parseFrameResponse decodes the answer to one frame: an acknowledgement when
// nothing happened, a batch of property events when something did, or a typed
// error. The batch carries every event of the frame, so a mid-stream
// satisfaction reaches the caller beside a violation rather than behind it.
func parseFrameResponse(raw string) (FrameResponse, error) {
	// Fast path: byte-level check before JSON parsing.
	if raw == ackCompact || raw == ackSpaced {
		return Ack{}, nil
	}

	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}

	if status := getString(m, "status"); status == "ack" {
		return Ack{}, nil
	} else if status == "error" {
		code := getString(m, "code")
		msg := getString(m, "message")
		if code != "" {
			return nil, newCodedError(ErrProtocol, code, msg)
		}
		return nil, protocolError(msg)
	}

	if respType := getString(m, "type"); respType == "property_batch" {
		rawResults := getArray(m, "results")
		if len(rawResults) == 0 {
			return nil, protocolError("property_batch response 'results' must be non-empty (zero-event frames are encoded as ack)")
		}
		results := make([]PropertyResult, 0, len(rawResults))
		for _, item := range rawResults {
			r, ok := item.(map[string]any)
			if !ok {
				return nil, protocolError("expected object in property_batch results array")
			}
			pr, err := parsePropertyResult(r)
			if err != nil {
				return nil, err
			}
			results = append(results, pr)
		}
		return PropertyBatch{Results: results}, nil
	}

	return nil, protocolError(fmt.Sprintf(
		"unexpected frame response: status=%q, type=%q",
		getString(m, "status"), getString(m, "type"),
	))
}

// parseStreamResponse decodes the end of a stream: one final verdict per
// property.
func parseStreamResponse(raw string) (*StreamResult, error) {
	m, err := decodeResponse(raw, "complete")
	if err != nil {
		return nil, err
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

	var warnings []StreamWarning
	for _, item := range getArray(m, "warnings") {
		w, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in warnings array")
		}
		idx, err := parseNumberAsInt64(w["property_index"])
		if err != nil {
			return nil, wrapProtocolError("warning property_index", err)
		}
		warnings = append(warnings, StreamWarning{
			Kind:          getString(w, "kind"),
			PropertyIndex: int(idx),
			Detail:        getString(w, "detail"),
		})
	}
	return &StreamResult{Results: results, Warnings: warnings}, nil
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
		return zero, wrapProtocolError("invalid property_index", err)
	}
	if idx < 0 {
		return zero, protocolError(fmt.Sprintf("negative property_index: %d", idx))
	}

	pr := PropertyResult{
		PropertyIndex: PropertyIndex(idx),
		Verdict:       verdict,
		Reason:        getString(r, "reason"),
	}

	// An absent key reads as nil, as a null one does: either is no timestamp.
	if tsRaw := r["timestamp"]; tsRaw != nil {
		ts, err := parseNumberAsInt64(tsRaw)
		if err != nil {
			return zero, wrapProtocolError("invalid timestamp in result", err)
		}
		if ts < 0 {
			return zero, protocolError(fmt.Sprintf("negative timestamp in result: %d", ts))
		}
		t := Timestamp{Microseconds: ts}
		pr.Timestamp = &t
	}

	return pr, nil
}
