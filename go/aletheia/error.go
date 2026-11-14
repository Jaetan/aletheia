// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"fmt"
)

// ErrBinaryPathUnsupported is what a Backend answers when it cannot serve
// the binary extraction path, as [MockBackend] cannot, having no library
// to call. It is the only error that falls through to the JSON path; see
// [Client.ExtractSignals].
var ErrBinaryPathUnsupported = errors.New("binary path not supported by this backend")

// ErrorKind classifies the source of an error.
type ErrorKind int

//go:generate stringer -type=ErrorKind -linecomment -output=errorkind_string.go

const (
	// ErrProtocol indicates a command or a response that does not cross as the
	// protocol says, or a refusal with a wire code that no typed error carries.
	ErrProtocol ErrorKind = iota // protocol
	// ErrValidation indicates input the caller supplied, refused by the binding's
	// own checks (DBC definition, formula/predicate values, check-loader input,
	// frame payload, …) or, for a decimal literal, by the kernel with its Code.
	ErrValidation // validation
	// ErrState indicates an operation was attempted in the wrong client state.
	ErrState // state
	// ErrFFI indicates a failure in the FFI layer (dlopen, dlsym, hs_init).
	ErrFFI // ffi
)

// Error is what every operation of this package returns on failure. Use
// [errors.As] to read its [ErrorKind] and [errors.Unwrap] for the cause.
type Error struct {
	// Kind is the high-level category: validation, state, protocol or FFI.
	Kind ErrorKind
	// Code is the kernel's or the shared library's wire code, empty for the
	// binding's own errors; the Code* constants below are the whole vocabulary.
	Code ErrorCode
	// Message is the human-readable diagnostic.
	Message string
	// Cause is the optional wrapped underlying error; nil when there is none.
	// Used by [errors.Unwrap] / [errors.Is] / [errors.As].
	Cause error
	// Location is where a loader read the number the kernel refused, such as
	// "Check 'C'" or "Row 2"; empty outside a loader. See [Locate].
	Location string
	// Key is the key or column header the refused number sat under, such as
	// "value" or "Factor"; empty outside a loader and for a refusal no single
	// key holds, such as a check its builder refused.
	Key string
}

// Error returns the message, the kernel's text when the kernel refused, as
// every binding prints it, with the cause after it when the error wraps one;
// the kind and the code are fields, not text. A refusal a loader located is
// led by the location and the key, as "<location>: invalid '<key>': ".
func (e *Error) Error() string {
	text := e.Message
	if e.Cause != nil {
		text += ": " + e.Cause.Error()
	}
	return locatedText(e.Location, e.Key, text)
}

// Unwrap returns the underlying error, enabling [errors.Is] and [errors.As].
func (e *Error) Unwrap() error { return e.Cause }

// ErrorCode is a machine-readable error code: the kernel's, or the shared
// library's own refusal of an entry's arguments.
type ErrorCode string

// The machine-readable error codes, one per error the kernel or the shared
// library can raise, grouped by the layer that raises them: parsing, DBC text,
// frames, input bounds, routing, handlers, dispatch and extraction, and last
// the shared library's own refusal of an entry's arguments. The string each
// one carries is the identifier on the wire and in [Error.Code], and
// docs/WIRE_CODES.yaml pins the whole vocabulary across the bindings.
const (
	// CodeParseMissingField — required JSON field absent on the input object.
	CodeParseMissingField ErrorCode = "parse_missing_field"
	// CodeParseInvalidByteOrder — byte_order value not "big" or "little".
	CodeParseInvalidByteOrder ErrorCode = "parse_invalid_byte_order"
	// CodeParseInvalidPresence — presence value not "always" or "muxed".
	CodeParseInvalidPresence ErrorCode = "parse_invalid_presence"
	// CodeParseMissingSigned — required `signed` field absent.
	CodeParseMissingSigned ErrorCode = "parse_missing_signed"
	// CodeParseInvalidSigned — `signed` field not boolean.
	CodeParseInvalidSigned ErrorCode = "parse_invalid_signed"
	// CodeParseNotAnObject — expected JSON object at this position.
	CodeParseNotAnObject ErrorCode = "parse_not_an_object"
	// CodeParseExtCanIDOutOfRange — extended CAN ID exceeds 29-bit range.
	CodeParseExtCanIDOutOfRange ErrorCode = "parse_ext_can_id_out_of_range"
	// CodeParseStdCanIDOutOfRange — standard CAN ID exceeds 11-bit range.
	CodeParseStdCanIDOutOfRange ErrorCode = "parse_std_can_id_out_of_range"
	// CodeParseDefaultCanIDOutOfRange — default CAN ID literal exceeds 29-bit range.
	CodeParseDefaultCanIDOutOfRange ErrorCode = "parse_default_can_id_out_of_range"
	// CodeParseInvalidDLCBytes — DLC byte count is not a valid CAN/CAN-FD value.
	CodeParseInvalidDLCBytes ErrorCode = "parse_invalid_dlc_bytes"
	// CodeParseRootNotObject — JSON root is not an object.
	CodeParseRootNotObject ErrorCode = "parse_root_not_object"
	// CodeParseMissingSignalName — required `name` field absent on a signal.
	CodeParseMissingSignalName ErrorCode = "parse_missing_signal_name"
	// CodeParseSignalBitLengthZero — signal has zero bit length.
	CodeParseSignalBitLengthZero ErrorCode = "parse_signal_bit_length_zero"
	// CodeParseSignalStartBitExceedsFrame — signal start bit lies outside the message's frame capacity.
	CodeParseSignalStartBitExceedsFrame ErrorCode = "parse_signal_start_bit_exceeds_frame"
	// CodeParseSignalBitLengthExceedsFrame — signal bit length exceeds the message's frame capacity.
	CodeParseSignalBitLengthExceedsFrame ErrorCode = "parse_signal_bit_length_exceeds_frame"
	// CodeParseSignalBigEndianOverflow — big-endian signal's descending bit run extends past the end of the frame.
	CodeParseSignalBigEndianOverflow ErrorCode = "parse_signal_big_endian_overflow"
	// CodeParseInvalidKind — kind tag not recognized.
	CodeParseInvalidKind ErrorCode = "parse_invalid_kind"
	// CodeParseNonTerminatingRational — rational value lacks a terminating decimal representation.
	CodeParseNonTerminatingRational ErrorCode = "parse_non_terminating_rational"
	// CodeParseInvalidIdentifier — identifier fails DBC's identifier syntax.
	CodeParseInvalidIdentifier ErrorCode = "parse_invalid_identifier"
	// CodeParseNonIntegerMultiplexValue — `multiplex_values` array contains a non-natural element.
	CodeParseNonIntegerMultiplexValue ErrorCode = "parse_non_integer_multiplex_value"
	// CodeParseNonNaturalField — a field is present but its value is not a JSON natural number.
	CodeParseNonNaturalField ErrorCode = "parse_non_natural_field"
	// CodeParseDLCCodeOutOfRange reports a frame's DLC code above 15.
	CodeParseDLCCodeOutOfRange ErrorCode = "parse_dlc_code_out_of_range"
	// CodeParsePayloadLengthMismatch reports a frame's payload length that is
	// not the byte count its DLC names.
	CodeParsePayloadLengthMismatch ErrorCode = "parse_payload_length_mismatch"
	// CodeParsePayloadByteOutOfRange reports a frame's payload byte of 256 or
	// above.
	CodeParsePayloadByteOutOfRange ErrorCode = "parse_payload_byte_out_of_range"
	// CodeParseNonPositiveDenominator reports a signal value whose denominator
	// is zero or negative.
	CodeParseNonPositiveDenominator ErrorCode = "parse_non_positive_denominator"
	// CodeParseSignalArrayLengthMismatch reports signal-value arrays (indices,
	// numerators, denominators) of different lengths.
	CodeParseSignalArrayLengthMismatch ErrorCode = "parse_signal_array_length_mismatch"
	// CodeParseTimestampPastWire reports a binary entry's timestamp above
	// 18446744073709551615, the 64-bit wire range (unreachable through the
	// C ABI, whose timestamp is a uint64_t).
	CodeParseTimestampPastWire ErrorCode = "parse_timestamp_past_wire"

	// CodeTextParseFailure reports a text the kernel's parser could not start
	// on, a .dbc text or a decimal literal, at the line and column it stopped.
	CodeTextParseFailure ErrorCode = "text_parse_failure"
	// CodeTextTrailingInput reports a text the parser read a statement of and
	// then found unparsed characters, a .dbc text or a decimal literal.
	CodeTextTrailingInput ErrorCode = "text_trailing_input"
	// CodeDBCTextAttributeRefinementFailed — BA_ value fails its BA_DEF_ refinement.
	CodeDBCTextAttributeRefinementFailed ErrorCode = "dbc_text_attribute_refinement_failed"

	// CodeFrameSignalNotFound — frame-level: signal name not declared on the message.
	CodeFrameSignalNotFound ErrorCode = "frame_signal_not_found"
	// CodeFrameSignalIndexOOB — frame-level: signal index out of range for the message.
	CodeFrameSignalIndexOOB ErrorCode = "frame_signal_index_oob"
	// CodeFrameValueOutOfRange — a requested signal value lies outside the
	// signal's declared [minimum, maximum].
	CodeFrameValueOutOfRange ErrorCode = "frame_value_out_of_range"
	// CodeFrameValueNotRepresentable — no integer raw value scales to a
	// requested signal value under the signal's factor and offset.
	CodeFrameValueNotRepresentable ErrorCode = "frame_value_not_representable"
	// CodeFrameSignalsOverlap — two signals requested by one build or update
	// occupy overlapping bit positions.
	CodeFrameSignalsOverlap ErrorCode = "frame_signals_overlap"
	// CodeFrameSignalPastFrameEnd — a signal's last bit lies past the end of the
	// frame the caller's DLC sizes, so its overhanging bits have nowhere to go.
	CodeFrameSignalPastFrameEnd ErrorCode = "frame_signal_past_frame_end"
	// CodeFrameCanIDNotFound — no message in the DBC has this CAN ID.
	CodeFrameCanIDNotFound ErrorCode = "frame_can_id_not_found"
	// CodeFrameCanIDMismatch — frame CAN ID disagrees with the message ID resolved by name.
	CodeFrameCanIDMismatch ErrorCode = "frame_can_id_mismatch"
	// CodeFrameSignalValueOutOfBounds — an extracted value outside the signal's
	// [min, max]; its message is the reason extraction reports for the signal.
	CodeFrameSignalValueOutOfBounds ErrorCode = "frame_signal_value_out_of_bounds"

	// CodeInputBoundExceeded is any input bound crossed at any parser
	// surface; the payload's bound_kind field says which.
	CodeInputBoundExceeded ErrorCode = "input_bound_exceeded"

	// CodeDBCInvalidCharacter — a character outside the DBC character set,
	// carried as code_point; located by field and index, or by line and column.
	CodeDBCInvalidCharacter ErrorCode = "dbc_invalid_character"
	// CodeDBCKeywordName — a DBC keyword used as a name, carried as keyword.
	CodeDBCKeywordName ErrorCode = "dbc_keyword_name"

	// CodeRouteMissingField — required field absent on a routed request.
	CodeRouteMissingField ErrorCode = "route_missing_field"
	// CodeRouteUnknownCommand — command name not recognized by the dispatcher.
	CodeRouteUnknownCommand ErrorCode = "route_unknown_command"
	// CodeRouteMissingCommandField reports a request with no `command` field.
	CodeRouteMissingCommandField ErrorCode = "route_missing_command_field"
	// CodeRouteMissingDBCField — `dbc` field absent on a request that requires it.
	CodeRouteMissingDBCField ErrorCode = "route_missing_dbc_field"
	// CodeRouteMissingPropsField — `properties` field absent on a request that requires it.
	CodeRouteMissingPropsField ErrorCode = "route_missing_props_field"

	// CodeHandlerNoDBC — handler invoked before any DBC was parsed.
	CodeHandlerNoDBC ErrorCode = "handler_no_dbc"
	// CodeHandlerAlreadyStreaming — start_stream called while a stream is active.
	CodeHandlerAlreadyStreaming ErrorCode = "handler_already_streaming"
	// CodeHandlerNotStreaming reports end_stream called outside a stream.
	CodeHandlerNotStreaming ErrorCode = "handler_not_streaming"
	// CodeHandlerStreamNotStarted reports a data frame sent with a DBC loaded
	// but no stream started.
	CodeHandlerStreamNotStarted ErrorCode = "handler_stream_not_started"
	// CodeHandlerStreamActive — operation cannot be performed while a stream is active.
	CodeHandlerStreamActive ErrorCode = "handler_stream_active"
	// CodeHandlerPropertyParseFailed — set_properties body could not be parsed.
	CodeHandlerPropertyParseFailed ErrorCode = "handler_property_parse_failed"
	// CodeHandlerPropertyRefused: a property or a time bound checked on its
	// own, before any session holds it, was refused.
	CodeHandlerPropertyRefused ErrorCode = "handler_property_refused"
	// CodeHandlerUnknownSignal — a property names a signal no signal of the
	// loaded DBC carries.
	CodeHandlerUnknownSignal ErrorCode = "handler_unknown_signal"
	// CodeHandlerValidationFailed — handler-level validation rejected the request.
	CodeHandlerValidationFailed ErrorCode = "handler_validation_failed"
	// CodeHandlerTextRoundtripFailed — FormatDBCText refused: emitted text does not re-parse to the input DBC.
	CodeHandlerTextRoundtripFailed ErrorCode = "handler_text_roundtrip_failed"
	// CodeHandlerNonMonotonicTimestamp — frame timestamp regressed relative to the previous frame.
	CodeHandlerNonMonotonicTimestamp ErrorCode = "handler_non_monotonic_timestamp"

	// CodeDispatchMissingTypeField — request object missing the `type` field.
	CodeDispatchMissingTypeField ErrorCode = "dispatch_missing_type_field"
	// CodeDispatchUnknownMessageType — `type` value not recognized.
	CodeDispatchUnknownMessageType ErrorCode = "dispatch_unknown_message_type"
	// CodeDispatchInvalidJSON — request body is not valid JSON.
	CodeDispatchInvalidJSON ErrorCode = "dispatch_invalid_json"
	// CodeDispatchRequestNotObject — request body is not a JSON object at root.
	CodeDispatchRequestNotObject ErrorCode = "dispatch_request_not_object"

	// CodeExtractionMuxValueMismatch — multiplexor value does not match the requested signal's mux selector.
	CodeExtractionMuxValueMismatch ErrorCode = "extraction_mux_value_mismatch"
	// CodeExtractionSignalPastFrameEnd — the signal's last bit lies past the end
	// of the frame that arrived, so the bits it names are not there to read.
	CodeExtractionSignalPastFrameEnd ErrorCode = "extraction_signal_past_frame_end"
	// CodeExtractionMuxSignalNotFound — multiplexor signal referenced by a muxed signal is missing.
	CodeExtractionMuxSignalNotFound ErrorCode = "extraction_mux_signal_not_found"
	// CodeExtractionMuxChainCycle — multiplexor chain references itself.
	CodeExtractionMuxChainCycle ErrorCode = "extraction_mux_chain_cycle"
	// CodeExtractionMuxExtractionFailed — multiplexor extraction step failed.
	CodeExtractionMuxExtractionFailed ErrorCode = "extraction_mux_extraction_failed"
	// CodeExtractionValueExceedsWireRange: the extracted exact value's reduced
	// numerator magnitude or denominator exceeds
	// 340282366920938463463374607431768211455, the bound the kernel holds on
	// both extraction paths.
	CodeExtractionValueExceedsWireRange ErrorCode = "extraction_value_exceeds_wire_range"

	// CodeFFIValidationError is the shared library's own refusal of an
	// argument it cannot read (a NULL pointer, a text that is not UTF-8 or
	// holds a NUL) or of a buffer smaller than the frame the kernel built.
	CodeFFIValidationError ErrorCode = "ffi_validation_error"
)

// errorCodes is every ErrorCode, the set a reply's error code is read from.
var errorCodes = map[ErrorCode]struct{}{
	CodeParseMissingField:                {},
	CodeParseInvalidByteOrder:            {},
	CodeParseInvalidPresence:             {},
	CodeParseMissingSigned:               {},
	CodeParseInvalidSigned:               {},
	CodeParseNotAnObject:                 {},
	CodeParseExtCanIDOutOfRange:          {},
	CodeParseStdCanIDOutOfRange:          {},
	CodeParseDefaultCanIDOutOfRange:      {},
	CodeParseInvalidDLCBytes:             {},
	CodeParseRootNotObject:               {},
	CodeParseMissingSignalName:           {},
	CodeParseSignalBitLengthZero:         {},
	CodeParseSignalStartBitExceedsFrame:  {},
	CodeParseSignalBitLengthExceedsFrame: {},
	CodeParseSignalBigEndianOverflow:     {},
	CodeParseInvalidKind:                 {},
	CodeParseNonTerminatingRational:      {},
	CodeParseInvalidIdentifier:           {},
	CodeParseNonIntegerMultiplexValue:    {},
	CodeParseNonNaturalField:             {},
	CodeParseDLCCodeOutOfRange:           {},
	CodeParsePayloadLengthMismatch:       {},
	CodeParsePayloadByteOutOfRange:       {},
	CodeParseNonPositiveDenominator:      {},
	CodeParseSignalArrayLengthMismatch:   {},
	CodeParseTimestampPastWire:           {},
	CodeTextParseFailure:                 {},
	CodeTextTrailingInput:                {},
	CodeDBCTextAttributeRefinementFailed: {},
	CodeFrameSignalNotFound:              {},
	CodeFrameSignalIndexOOB:              {},
	CodeFrameValueOutOfRange:             {},
	CodeFrameValueNotRepresentable:       {},
	CodeFrameSignalsOverlap:              {},
	CodeFrameSignalPastFrameEnd:          {},
	CodeFrameCanIDNotFound:               {},
	CodeFrameCanIDMismatch:               {},
	CodeFrameSignalValueOutOfBounds:      {},
	CodeInputBoundExceeded:               {},
	CodeDBCInvalidCharacter:              {},
	CodeDBCKeywordName:                   {},
	CodeRouteMissingField:                {},
	CodeRouteUnknownCommand:              {},
	CodeRouteMissingCommandField:         {},
	CodeRouteMissingDBCField:             {},
	CodeRouteMissingPropsField:           {},
	CodeHandlerNoDBC:                     {},
	CodeHandlerAlreadyStreaming:          {},
	CodeHandlerNotStreaming:              {},
	CodeHandlerStreamNotStarted:          {},
	CodeHandlerStreamActive:              {},
	CodeHandlerPropertyParseFailed:       {},
	CodeHandlerPropertyRefused:           {},
	CodeHandlerUnknownSignal:             {},
	CodeHandlerValidationFailed:          {},
	CodeHandlerTextRoundtripFailed:       {},
	CodeHandlerNonMonotonicTimestamp:     {},
	CodeDispatchMissingTypeField:         {},
	CodeDispatchUnknownMessageType:       {},
	CodeDispatchInvalidJSON:              {},
	CodeDispatchRequestNotObject:         {},
	CodeExtractionMuxValueMismatch:       {},
	CodeExtractionSignalPastFrameEnd:     {},
	CodeExtractionMuxSignalNotFound:      {},
	CodeExtractionMuxChainCycle:          {},
	CodeExtractionMuxExtractionFailed:    {},
	CodeExtractionValueExceedsWireRange:  {},
	CodeFFIValidationError:               {},
}

// locatedText is an error's text as it prints: after the location and the
// key when a loader located it, after the location alone when no key holds
// the refusal, alone otherwise.
func locatedText(location, key, text string) string {
	switch {
	case location == "":
		return text
	case key == "":
		return location + ": " + text
	default:
		return location + ": invalid '" + key + "': " + text
	}
}

// Locate is a refusal of the kernel located where a loader read the refused
// number: the loaders know where the number was, and the kernel, handed its
// text alone, does not. A coded *Error or an *InputBoundExceededError comes
// back as a copy carrying the location and the key, the kernel's kind, code,
// message and fields unchanged; any other error comes back as it was given.
func Locate(err error, location, key string) error {
	switch e := err.(type) {
	case *Error:
		if e.Code != "" {
			located := *e
			located.Location, located.Key = location, key
			return &located
		}
	case *InputBoundExceededError:
		located := *e
		located.Location, located.Key = location, key
		return &located
	}
	return err
}

// locateRefusal locates a refusal no single key holds, such as a check its
// builder refused: a coded refusal no reader located gains location and no
// key; one a reader located, or one without a code (the runtime down, a
// malformed reply), comes back as it was.
func locateRefusal(err error, location string) error {
	switch e := err.(type) {
	case *Error:
		if e.Code != "" && e.Location == "" {
			return Locate(err, location, "")
		}
	case *InputBoundExceededError:
		if e.Location == "" {
			return Locate(err, location, "")
		}
	}
	return err
}

// newError builds a typed *Error without a wire code or inner cause.
func newError(kind ErrorKind, msg string) *Error {
	return &Error{Kind: kind, Message: msg}
}

// newCodedError builds a typed *Error carrying a wire Code (one of the
// Code* constants above), which a caller reaches with errors.As and
// matches on.
func newCodedError(kind ErrorKind, code ErrorCode, msg string) *Error {
	return &Error{Kind: kind, Code: code, Message: msg}
}

// wrapError attaches an inner cause to a typed *Error; the Unwrap
// method returns the cause for use with errors.Is / errors.As.
func wrapError(kind ErrorKind, msg string, cause error) *Error {
	return &Error{Kind: kind, Message: msg, Cause: cause}
}

// protocolError reports a wire-level mismatch between Go and the Agda core.
func protocolError(msg string) *Error { return newError(ErrProtocol, msg) }

// validationError reports user-supplied input that failed local validation.
func validationError(msg string) *Error { return newError(ErrValidation, msg) }

// stateError reports a lifecycle violation (closed client, double close, …).
func stateError(msg string) *Error { return newError(ErrState, msg) }

// ffiError reports failures inside the dlopen/dlsym/hs_init path.
func ffiError(msg string) *Error { return newError(ErrFFI, msg) }

// wrapProtocolError is the wrap variant of protocolError for JSON decode / I/O failures.
func wrapProtocolError(msg string, cause error) *Error { return wrapError(ErrProtocol, msg, cause) }

// wrapValidationError is the wrap variant of validationError for nested parse failures.
func wrapValidationError(msg string, cause error) *Error { return wrapError(ErrValidation, msg, cause) }

// NewValidationError returns an [ErrValidation] error with the message. It
// is exported so a loader outside this package, such as the Excel module,
// reports failures in the shape the built-in loaders do.
func NewValidationError(msg string) *Error { return validationError(msg) }

// WrapValidationError is [NewValidationError] over an underlying cause.
func WrapValidationError(msg string, cause error) *Error {
	return wrapValidationError(msg, cause)
}

// InputBoundExceededError reports an input bound the kernel refused, or one
// the binding checks itself before the call, with the bound, what was
// observed, the limit, the kernel's message and the part of the input that
// crossed it, when the refusal names one. It is the kernel's
// InputBoundExceeded, and the peer bindings carry the same type: Python's
// InputBoundExceededError, the C++ aletheia::InputBoundExceededError and
// the Rust Error::InputBoundExceeded.
//
// Use [errors.As] to inspect it, as the example does.
type InputBoundExceededError struct {
	// BoundKind names the bound, one of the BoundKind constants in limits.go.
	BoundKind string
	// Observed is the measured value that exceeded the limit, or 2^128-1
	// when the kernel measured more, its message then naming no number.
	Observed Uint128
	// Limit is the bound itself.
	Limit Uint128
	// Code is the wire error code, always [CodeInputBoundExceeded]: the
	// decoder lifts this type for no other.
	Code ErrorCode
	// Field names the part of the input that crossed the bound, as the
	// kernel's refusal names it: a DBC's "senders array" or "signal factor",
	// a decimal given to FromDecimal as "decimal". It is empty when the
	// refusal names none, as for a bound on the input's length, its nesting
	// depth or an identifier's length.
	Field string
	// Message is the kernel's message for the refusal, such as "ParseDBC:
	// senders array: array cardinality 10001 exceeds limit 10000". It is
	// empty for a bound the binding checks itself before the call.
	Message string
	// Location is where a loader read the number the kernel refused, as on
	// [Error]; empty outside a loader. See [Locate].
	Location string
	// Key is the key or column header the refused number sat under; empty
	// outside a loader and for a refusal no single key holds.
	Key string
}

// Error returns the kernel's message, and for a bound the binding checks
// itself, which has none, the binding's own text naming the kind, the size
// and the limit. A refusal a loader located is led by the location and the
// key, as [Error.Error] prints one.
func (e *InputBoundExceededError) Error() string {
	text := e.Message
	if text == "" {
		text = fmt.Sprintf("%s %s exceeds limit %s", e.BoundKind, e.Observed, e.Limit)
	}
	return locatedText(e.Location, e.Key, text)
}

// newInputBoundExceededError builds the typed error, for the lifter in
// json_response.go and for the bounds the binding checks before the call, which name
// no field and carry no message.
func newInputBoundExceededError(kind string, observed, limit Uint128, code ErrorCode, field, message string) *InputBoundExceededError {
	return &InputBoundExceededError{
		BoundKind: kind,
		Observed:  observed,
		Limit:     limit,
		Code:      code,
		Field:     field,
		Message:   message,
	}
}

// ValidationFailedError reports a DBC that parsed but failed structural
// validation with at least one error-severity issue, as [Client.ParseDBC]
// and [Client.ParseDBCText] refuse it. The issues have the element shape
// of a validation response. Python raises DBCValidationFailedError and
// Rust returns Error::ValidationFailed for the same refusal; C++ carries
// it on its one error class, under ErrorCode::HandlerValidationFailed.
//
// Use [errors.As] to inspect it, as the example does.
type ValidationFailedError struct {
	// Issues are the structural validation findings in wire order,
	// with the same element shape as [ValidationResult].Issues.
	Issues []ValidationIssue
	// HasErrors reports whether any issue has error severity; it is read
	// from the wire rather than assumed, though the kernel sets it here.
	HasErrors bool
	// Code is the wire error code, always [CodeHandlerValidationFailed]:
	// the decoder lifts this type for no other.
	Code ErrorCode
	// Message is the envelope's human-readable diagnostic.
	Message string
}

// Error returns the kernel's message, as a generic coded protocol error with
// the same message prints, so a caller that only prints it sees one shape;
// the issues are fields.
func (e *ValidationFailedError) Error() string { return e.Message }

// newValidationFailedError builds the typed error from a decoded envelope,
// for validationFailedFromResponse in json_response.go.
func newValidationFailedError(issues []ValidationIssue, hasErrors bool, code ErrorCode, msg string) *ValidationFailedError {
	return &ValidationFailedError{
		Issues:    issues,
		HasErrors: hasErrors,
		Code:      code,
		Message:   msg,
	}
}

// TextRoundTripFailedError reports that [Client.FormatDBCText] refused: the
// text it would emit does not re-parse to the DBC given, and it returns
// text only when it provably does. The issues lead with the divergence
// itself and have the element shape of a validation response, which is the
// shape [ValidationFailedError] carries for a different refusal. Python
// raises TextRoundTripFailedError and Rust returns
// Error::TextRoundtripFailed; C++ carries it on its one error class, under
// ErrorCode::HandlerTextRoundtripFailed.
//
// Use [errors.As] to inspect it, as the example does.
type TextRoundTripFailedError struct {
	// Issues are the round-trip diagnostics in wire order, led by the
	// error-severity text_roundtrip_divergence issue.
	Issues []ValidationIssue
	// HasErrors reports whether any issue has error severity; it is read
	// from the wire rather than assumed.
	HasErrors bool
	// Code is the wire error code, always [CodeHandlerTextRoundtripFailed]:
	// the decoder lifts this type for no other.
	Code ErrorCode
	// Message is the envelope's human-readable diagnostic.
	Message string
}

// Error returns the kernel's message, as [ValidationFailedError.Error] does.
func (e *TextRoundTripFailedError) Error() string { return e.Message }

// newTextRoundTripFailedError builds the typed error from a decoded
// envelope, for textRoundtripFailedFromResponse in json_response.go.
func newTextRoundTripFailedError(issues []ValidationIssue, hasErrors bool, code ErrorCode, msg string) *TextRoundTripFailedError {
	return &TextRoundTripFailedError{
		Issues:    issues,
		HasErrors: hasErrors,
		Code:      code,
		Message:   msg,
	}
}
