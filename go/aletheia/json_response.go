// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/binary"
	"encoding/json"
	"fmt"
	"slices"
	"strings"
	"unicode/utf8"
)

// --- Deserialization: the kernel's JSON to Go ---

// Every reader below requires each key the kernel writes and reads each place
// by kind, refusing what the kernel never writes there in the one form of
// reply_shape.go: the ranges and the tags are the kernel's, proven of every
// reply. A validation issue's severity and code, an error reply's code, a
// property result's type and status and a stream warning's kind are read as a
// member of their set, any other refused at its place, and
// tools/check_limits_parity.py compares the words each tag's reader awaits
// with the reply proof's.

// expectJSONText is what a reply's text holds before it is read as an object.
const expectJSONText = "JSON text"

// jsonSpace is the whitespace JSON allows around a value.
const jsonSpace = " \t\r\n"

// parseResponse reads a kernel reply into a generic map, which the typed
// decoders below narrow.
//
// Numbers arrive as decimal strings rather than float64, so a numerator or
// denominator past 2^53 survives. Text that is not one JSON value is refused
// with the decoder's reason, and a value that is not an object by its kind.
func parseResponse(raw string) (map[string]any, error) {
	dec := json.NewDecoder(strings.NewReader(raw))
	dec.UseNumber()
	var v any
	err := dec.Decode(&v)
	if err == nil && strings.TrimLeft(raw[dec.InputOffset():], jsonSpace) != "" {
		// The decoder stops after the first value; json.Unmarshal reads the
		// whole text and names what follows it.
		err = json.Unmarshal([]byte(raw), new(json.RawMessage))
	}
	if err != nil {
		return nil, replyRefusal("", expectJSONText, err.Error())
	}
	return readObject(v, "")
}

// replyStatus is the status at a reply's root, a struct so that no untyped
// string stands for one. The readers await no status but the values below,
// which tools/check_limits_parity.py compares with the words the reply proof
// gives the place, refusing a status built anywhere else in the package.
type replyStatus struct{ word string }

// The answer each command awaits, and the error any command may answer.
var (
	statusSuccess    = replyStatus{"success"}
	statusValidation = replyStatus{"validation"}
	statusComplete   = replyStatus{"complete"}
	statusAck        = replyStatus{"ack"}
	statusError      = replyStatus{"error"}
)

// decodeResponse reads a reply whose status is the one the command answers or
// "error", and lifts an error into its typed error. Every typed decoder below
// opens with it, so a reply that is malformed, an error, or not the answer to
// the command asked is refused in one place.
func decodeResponse(raw string, want replyStatus) (map[string]any, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	status, err := fieldStatus(m, "", "status", want, statusError)
	if err != nil {
		return nil, err
	}
	if status == statusError {
		return nil, checkErrorStatus(m)
	}
	return m, nil
}

// checkErrorStatus reads an error envelope into the error it carries, and
// never answers nil. The envelope's status is "error", its code one of the
// ErrorCodes and its message a string; where the code carries a payload of its
// own, one of the lifts below gives the caller a type to match on instead of
// the generic coded error. A place of the envelope holding what the kernel
// never writes there is refused.
func checkErrorStatus(m map[string]any) error {
	if _, err := fieldStatus(m, "", "status", statusError); err != nil {
		return err
	}
	code, err := fieldMember(m, "", "code", expectErrorCode, errorCodes)
	if err != nil {
		return err
	}
	msg, err := fieldString(m, "", "message")
	if err != nil {
		return err
	}
	bex, err := inputBoundExceededFromResponse(code, msg, m)
	if err != nil {
		return err
	}
	if bex != nil {
		return bex
	}
	vfe, err := validationFailedFromResponse(code, msg, m)
	if err != nil {
		return err
	}
	if vfe != nil {
		return vfe
	}
	trte, err := textRoundtripFailedFromResponse(code, msg, m)
	if err != nil {
		return err
	}
	if trte != nil {
		return trte
	}
	return newCodedError(ErrProtocol, code, msg)
}

// The three lifts below turn a coded error envelope into the typed error a
// caller can match on. Each answers nil for an envelope of another code, and
// refuses a payload its code carries that is not whole.

// boundTripleKeys are the keys of a bound refusal's triple.
var boundTripleKeys = [...]string{"bound_kind", "observed", "limit"}

// boundTriple is the bound a refusal says was crossed: its kind, the size
// observed and the limit.
type boundTriple struct {
	kind            string
	observed, limit Uint128
}

// readBoundTriple reads a bound refusal's triple, false when the envelope
// holds none of its keys. An envelope holding any of them holds all three,
// each broken key refused at its place; the kernel proves the observed size
// and the limit positive, so they are read without a range check.
func readBoundTriple(m map[string]any) (boundTriple, bool, error) {
	held := slices.ContainsFunc(boundTripleKeys[:], func(key string) bool {
		_, ok := m[key]
		return ok
	})
	if !held {
		return boundTriple{}, false, nil
	}
	kind, err := fieldString(m, "", "bound_kind")
	if err != nil {
		return boundTriple{}, false, err
	}
	observed, err := fieldUint128(m, "", "observed")
	if err != nil {
		return boundTriple{}, false, err
	}
	limit, err := fieldUint128(m, "", "limit")
	if err != nil {
		return boundTriple{}, false, err
	}
	return boundTriple{kind: kind, observed: observed, limit: limit}, true, nil
}

// boundField reads the part of the input a bound refusal names, "" when it
// names none.
func boundField(m map[string]any) (string, error) {
	if _, named := m["field"]; !named {
		return "", nil
	}
	return fieldString(m, "", "field")
}

// inputBoundExceededFromResponse lifts a bound refusal, whichever bound the
// kernel crossed. An envelope of any code holding part of the triple holds it
// whole with a string field, if it names one, and a bound refusal holds the
// triple always. The typed error keeps the kind, the observed size, the limit,
// the field the refusal names, if it names one, and the kernel's message,
// which is its text.
func inputBoundExceededFromResponse(code ErrorCode, msg string, m map[string]any) (*InputBoundExceededError, error) {
	triple, held, err := readBoundTriple(m)
	if err != nil {
		return nil, err
	}
	if !held {
		if code == CodeInputBoundExceeded {
			return nil, replyRefusal("bound_kind", expectString, came(m, "bound_kind"))
		}
		return nil, nil
	}
	field, err := boundField(m)
	if err != nil {
		return nil, err
	}
	if code != CodeInputBoundExceeded {
		return nil, nil
	}
	return newInputBoundExceededError(triple.kind, triple.observed, triple.limit, code, field, msg), nil
}

// issuesPayload reads the has_errors flag and the issues an envelope carries,
// a validation reply or a DBC refusal, both of which the kernel writes on it.
func issuesPayload(m map[string]any) ([]ValidationIssue, bool, error) {
	hasErrors, err := fieldBool(m, "", "has_errors")
	if err != nil {
		return nil, false, err
	}
	issues, err := parseIssueArray(m, "issues")
	if err != nil {
		return nil, false, err
	}
	return issues, hasErrors, nil
}

// validationFailedFromResponse lifts a refusal of a DBC that failed
// validation. The issues have the element shape of a validation reply, and
// the wire message is carried through, so the rendered error is what the
// generic one rendered.
func validationFailedFromResponse(code ErrorCode, msg string, m map[string]any) (*ValidationFailedError, error) {
	if code != CodeHandlerValidationFailed {
		return nil, nil
	}
	issues, hasErrors, err := issuesPayload(m)
	if err != nil {
		return nil, err
	}
	return newValidationFailedError(issues, hasErrors, code, msg), nil
}

// textRoundtripFailedFromResponse lifts a refusal of a DBC whose text does not
// re-parse, carrying the same payload as the validation refusal above.
func textRoundtripFailedFromResponse(code ErrorCode, msg string, m map[string]any) (*TextRoundTripFailedError, error) {
	if code != CodeHandlerTextRoundtripFailed {
		return nil, nil
	}
	issues, hasErrors, err := issuesPayload(m)
	if err != nil {
		return nil, err
	}
	return newTextRoundTripFailedError(issues, hasErrors, code, msg), nil
}

// parseSuccessResponse is the answer to a control-plane command that carries
// nothing but its success.
func parseSuccessResponse(raw string) error {
	_, err := decodeResponse(raw, statusSuccess)
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
	_, err := decodeResponse(raw, statusAck)
	return err
}

// parseIssueArray decodes the validation issues at key of a reply's root, for
// the validation reply, the warnings of a parsed DBC and the issues of a DBC
// refusal. The result is empty rather than nil, so encoding it again writes an
// empty array and not a null, which is what the Python decoder answers.
func parseIssueArray(m map[string]any, key string) ([]ValidationIssue, error) {
	entries, err := fieldArray(m, "", key)
	if err != nil {
		return nil, err
	}
	place := replyPath(key)
	issues := make([]ValidationIssue, 0, len(entries))
	for _, entry := range entries {
		issue, err := readObject(entry, place)
		if err != nil {
			return nil, err
		}
		code, err := fieldMember(issue, place, "code", expectIssueCode, issueCodes)
		if err != nil {
			return nil, err
		}
		detail, err := fieldString(issue, place, "detail")
		if err != nil {
			return nil, err
		}
		severity, err := readSeverity(issue, place)
		if err != nil {
			return nil, err
		}
		issues = append(issues, ValidationIssue{Severity: severity, Code: code, Detail: detail})
	}
	return issues, nil
}

// readSeverity reads an issue's severity, "error" or "warning".
func readSeverity(issue map[string]any, path replyPath) (IssueSeverity, error) {
	word, err := fieldWord(issue, path, "severity", "error", "warning")
	if err != nil {
		return 0, err
	}
	if word == "error" {
		return SeverityError, nil
	}
	return SeverityWarning, nil
}

// parseValidationResponse decodes a validateDBC response into typed
// ValidationIssues, preserving severity and the Agda error code.
func parseValidationResponse(raw string) (*ValidationResult, error) {
	m, err := decodeResponse(raw, statusValidation)
	if err != nil {
		return nil, err
	}
	issues, hasErrors, err := issuesPayload(m)
	if err != nil {
		return nil, err
	}
	return &ValidationResult{HasErrors: hasErrors, Issues: issues}, nil
}

// parseExtractionResponse decodes an extractAllSignals JSON response.
// Binary-extraction responses use parseExtractionBin instead.
func parseExtractionResponse(raw string) (*ExtractionResult, error) {
	m, err := decodeResponse(raw, statusSuccess)
	if err != nil {
		return nil, err
	}
	values, err := fieldObjects(m, "", "values", readSignalValue)
	if err != nil {
		return nil, err
	}
	signalErrors, err := fieldObjects(m, "", "errors", readSignalError)
	if err != nil {
		return nil, err
	}
	absent, err := fieldStrings[SignalName](m, "", "absent")
	if err != nil {
		return nil, err
	}
	result := &ExtractionResult{Values: values, Errors: signalErrors, Absent: absent}
	result.buildIndex()
	return result, nil
}

// readSignalValue reads one extracted value at path: the signal's name and its
// exact value.
func readSignalValue(v map[string]any, path replyPath) (SignalValue, error) {
	name, err := fieldString(v, path, "name")
	if err != nil {
		return SignalValue{}, err
	}
	value, err := fieldRational(v, path, "value")
	if err != nil {
		return SignalValue{}, err
	}
	return SignalValue{Name: SignalName(name), Value: value}, nil
}

// readSignalError reads one extraction error at path: the signal's name and
// the kernel's reason.
func readSignalError(e map[string]any, path replyPath) (SignalError, error) {
	name, err := fieldString(e, path, "name")
	if err != nil {
		return SignalError{}, err
	}
	reason, err := fieldString(e, path, "error")
	if err != nil {
		return SignalError{}, err
	}
	return SignalError{Name: SignalName(name), Error: reason}, nil
}

// parseFrameDataResponse reads a payload out of a JSON response. Only the mock
// backend answers this way; the library returns the bytes themselves.
func parseFrameDataResponse(raw string) (FramePayload, error) {
	m, err := decodeResponse(raw, statusSuccess)
	if err != nil {
		return nil, err
	}
	data, err := fieldArray(m, "", "data")
	if err != nil {
		return nil, err
	}
	place := replyPath("data")
	payload := make(FramePayload, len(data))
	for i, item := range data {
		n, err := readUint64(item, place)
		if err != nil {
			return nil, err
		}
		// A number past a byte, which the kernel never writes, is refused as
		// the number the place does not hold.
		b := byte(n)
		if uint64(b) != n {
			return nil, replyRefusal(place, expectNumber, cameAs(item))
		}
		payload[i] = b
	}
	return payload, nil
}

// The binary extraction buffer's fixed sizes: the header, and one value entry.
const (
	extractionHeaderSize = 10
	extractionValueSize  = 35
)

// parseExtractionBin parses a packed binary extraction buffer into an ExtractionResult.
//
// Buffer layout (canonical wire doc: the processExtractBin header comment in
// src/Aletheia/Main/Binary.agda):
//
//	Header:  [nvals:u16][nerrs:u16][nabss:u16][reasonBytes:u32]  (10 bytes)
//	Values:  nvals × (idx:u16, negative:u8, num:u128, den:u128)  (35 bytes each)
//	Errors:  nerrs × (idx:u16, code:u8)                          (3 bytes each)
//	Offsets: (nerrs+1) x u32, cumulative byte offsets into Reasons;
//	         off[0] = 0, monotone non-decreasing, off[nerrs] = reasonBytes.
//	Reasons: reasonBytes of UTF-8; error i's reason = bytes [off[i], off[i+1]).
//	Absent:  nabss × (idx:u16)                                   (2 bytes each)
//
// Every word is little-endian, each u128 its low u64 then its high u64, and
// any sign byte but 0 is negative. The kernel proves every index below the
// count of the names, the signals of the frame's message, so each indexes
// them directly.
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
	if len(buf) < extractionHeaderSize+4 {
		return nil, protocolError("extraction binary buffer too short")
	}
	nvals := int(binary.LittleEndian.Uint16(buf[0:2]))
	nerrs := int(binary.LittleEndian.Uint16(buf[2:4]))
	nabss := int(binary.LittleEndian.Uint16(buf[4:6]))
	reasonBytes := int(binary.LittleEndian.Uint32(buf[6:10]))

	// The size must be exact, short and long alike: either means the writer and
	// this reader disagree about the layout.
	want := extractionHeaderSize + extractionValueSize*nvals + 3*nerrs + 4*(nerrs+1) + reasonBytes + 2*nabss
	if len(buf) != want {
		return nil, protocolError(fmt.Sprintf("extraction binary buffer size mismatch: got %d bytes, want %d", len(buf), want))
	}
	off := extractionHeaderSize

	result := &ExtractionResult{
		Values: make([]SignalValue, 0, nvals),
		Errors: make([]SignalError, 0, nerrs),
		Absent: make([]SignalName, 0, nabss),
	}

	for range nvals {
		idx := binary.LittleEndian.Uint16(buf[off:])
		numerator := uint128At(buf[off+3:])
		// The rational is the kernel's own, never rounded; a zero is unsigned,
		// as the JSON path reads it.
		value := Rational{
			Negative:    buf[off+2] != 0 && numerator != (Uint128{}),
			Numerator:   numerator,
			Denominator: uint128At(buf[off+19:]),
		}
		off += extractionValueSize
		result.Values = append(result.Values, SignalValue{Name: SignalName(names[idx]), Value: value})
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
		result.Errors = append(result.Errors, SignalError{Name: SignalName(names[idx]), Error: string(reason)})
	}
	off = reasonsAt + reasonBytes

	for range nabss {
		idx := binary.LittleEndian.Uint16(buf[off:])
		off += 2
		result.Absent = append(result.Absent, SignalName(names[idx]))
	}

	result.buildIndex()
	return result, nil
}

// uint128At reads the 128-bit word at the front of b: its low u64, then its
// high u64.
func uint128At(b []byte) Uint128 {
	return Uint128{Lo: binary.LittleEndian.Uint64(b), Hi: binary.LittleEndian.Uint64(b[8:])}
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

	// A batch carries no status of its own, each of its events carrying one,
	// and is told by its type.
	if _, hasStatus := m["status"]; hasStatus {
		status, err := fieldStatus(m, "", "status", statusAck, statusError)
		if err != nil {
			return nil, err
		}
		if status == statusAck {
			return Ack{}, nil
		}
		return nil, checkErrorStatus(m)
	}
	if _, err := fieldWord(m, "", "type", "property_batch"); err != nil {
		return nil, err
	}
	results, err := fieldObjects(m, "", "results", parsePropertyEvent)
	if err != nil {
		return nil, err
	}
	return PropertyBatch{Results: results}, nil
}

// parseStreamResponse decodes the end of a stream: one final verdict per
// property, and the warnings the kernel raised.
func parseStreamResponse(raw string) (*StreamResult, error) {
	m, err := decodeResponse(raw, statusComplete)
	if err != nil {
		return nil, err
	}
	results, err := fieldObjects(m, "", "results", parsePropertyResult)
	if err != nil {
		return nil, err
	}
	warnings, err := fieldObjects(m, "", "warnings", parseStreamWarning)
	if err != nil {
		return nil, err
	}
	return &StreamResult{Results: results, Warnings: warnings}, nil
}

// parseStreamWarning reads one end-of-stream warning at path: its kind, its
// property's index and its detail.
func parseStreamWarning(w map[string]any, path replyPath) (StreamWarning, error) {
	if _, err := fieldWord(w, path, "kind", "uncached_atom"); err != nil {
		return StreamWarning{}, err
	}
	index, err := fieldUint64(w, path, "property_index")
	if err != nil {
		return StreamWarning{}, err
	}
	detail, err := fieldString(w, path, "detail")
	if err != nil {
		return StreamWarning{}, err
	}
	return StreamWarning{Kind: WarningUncachedAtom, PropertyIndex: int(index), Detail: detail}, nil
}

// parsePropertyEvent reads one event of a frame's batch at path: its verdict,
// the timestamp of the frame that broke the property on a failure, and a
// reason on every verdict but a hold.
func parsePropertyEvent(r map[string]any, path replyPath) (PropertyResult, error) {
	pr, err := readVerdict(r, path)
	if err != nil {
		return PropertyResult{}, err
	}
	if pr.Verdict == Fails {
		if pr.Timestamp, err = readTimestamp(r, path); err != nil {
			return PropertyResult{}, err
		}
	}
	if pr.Verdict != Holds {
		if pr.Reason, err = fieldString(r, path, "reason"); err != nil {
			return PropertyResult{}, err
		}
	}
	return pr, nil
}

// parsePropertyResult reads one end-of-stream verdict at path into the typed
// PropertyResult sum (Satisfaction / Violation / Unresolved). A failure carries
// the timestamp of the frame that broke the property, and an unresolved
// verdict a timestamp only where its key holds one: an absent or null key is
// no timestamp.
func parsePropertyResult(r map[string]any, path replyPath) (PropertyResult, error) {
	pr, err := readVerdict(r, path)
	if err != nil {
		return PropertyResult{}, err
	}
	if pr.Verdict == Holds {
		return pr, nil
	}
	if ts, held := r["timestamp"]; pr.Verdict == Fails || (held && ts != nil) {
		if pr.Timestamp, err = readTimestamp(r, path); err != nil {
			return PropertyResult{}, err
		}
	}
	if pr.Reason, err = fieldString(r, path, "reason"); err != nil {
		return PropertyResult{}, err
	}
	return pr, nil
}

// readVerdict reads the type, the status and the property index every
// verdict carries, "unresolved" the status's last arm.
func readVerdict(r map[string]any, path replyPath) (PropertyResult, error) {
	if _, err := fieldWord(r, path, "type", "property"); err != nil {
		return PropertyResult{}, err
	}
	status, err := fieldWord(r, path, "status", "fails", "holds", "unresolved")
	if err != nil {
		return PropertyResult{}, err
	}
	index, err := fieldUint64(r, path, "property_index")
	if err != nil {
		return PropertyResult{}, err
	}
	var verdict Verdict
	switch status {
	case "fails":
		verdict = Fails
	case "holds":
		verdict = Holds
	default:
		verdict = Unresolved
	}
	return PropertyResult{PropertyIndex: PropertyIndex(index), Verdict: verdict}, nil
}

// readTimestamp reads the timestamp at path, which echoes a frame's: the
// binding sends every timestamp as an int64, so a number past one, which the
// kernel never writes back, is refused as the number the place does not hold.
func readTimestamp(r map[string]any, path replyPath) (*Timestamp, error) {
	n, err := fieldUint64(r, path, "timestamp")
	if err != nil {
		return nil, err
	}
	t := Timestamp{Microseconds: int64(n)}
	if t.Microseconds < 0 {
		return nil, replyRefusal(path.at("timestamp"), expectNumber, came(r, "timestamp"))
	}
	return &t, nil
}
