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
	// ErrProtocol indicates a JSON parsing or protocol mismatch with the Agda core.
	ErrProtocol ErrorKind = iota // protocol
	// ErrValidation indicates user-supplied input that failed local validation
	// (DBC definition, formula/predicate values, check-loader input, frame payload, …).
	ErrValidation // validation
	// ErrState indicates an operation was attempted in the wrong client state.
	ErrState // state
	// ErrFFI indicates a failure in the FFI layer (dlopen, dlsym, hs_init).
	ErrFFI // ffi
)

// Error is what every operation of this package returns on failure. Use
// [errors.As] to read its [ErrorKind] and [errors.Unwrap] for the cause.
type Error struct {
	// Kind is the high-level category (validation / state / protocol / FFI / ...).
	Kind ErrorKind
	// Code is the machine-readable wire code from the Agda core; empty for client-side errors.
	// See the Code* constants below for the full vocabulary.
	Code string
	// Message is the human-readable diagnostic.
	Message string
	// Cause is the optional wrapped underlying error; nil when there is none.
	// Used by [errors.Unwrap] / [errors.Is] / [errors.As].
	Cause error
}

// Error renders as "aletheia <kind> error: <message>", with the cause
// appended when there is one.
func (e *Error) Error() string {
	if e.Cause != nil {
		return fmt.Sprintf("aletheia %s error: %s: %s", e.Kind, e.Message, e.Cause)
	}
	return fmt.Sprintf("aletheia %s error: %s", e.Kind, e.Message)
}

// Unwrap returns the underlying error, enabling [errors.Is] and [errors.As].
func (e *Error) Unwrap() error { return e.Cause }

// The machine-readable error codes, one per error the kernel can raise,
// grouped by the layer that raises them: parsing, DBC text, frames, input
// bounds, routing, handlers, dispatch and extraction. The string each one
// carries is the identifier on the wire and in [Error.Code], and
// docs/WIRE_CODES.yaml pins the whole vocabulary across the bindings.
const (
	// CodeParseMissingField — required JSON field absent on the input object.
	CodeParseMissingField = "parse_missing_field"
	// CodeParseInvalidByteOrder — byte_order value not "big" or "little".
	CodeParseInvalidByteOrder = "parse_invalid_byte_order"
	// CodeParseInvalidPresence — presence value not "always" or "muxed".
	CodeParseInvalidPresence = "parse_invalid_presence"
	// CodeParseMissingSigned — required `signed` field absent.
	CodeParseMissingSigned = "parse_missing_signed"
	// CodeParseInvalidSigned — `signed` field not boolean.
	CodeParseInvalidSigned = "parse_invalid_signed"
	// CodeParseNotAnObject — expected JSON object at this position.
	CodeParseNotAnObject = "parse_not_an_object"
	// CodeParseExtCanIDOutOfRange — extended CAN ID exceeds 29-bit range.
	CodeParseExtCanIDOutOfRange = "parse_ext_can_id_out_of_range"
	// CodeParseStdCanIDOutOfRange — standard CAN ID exceeds 11-bit range.
	CodeParseStdCanIDOutOfRange = "parse_std_can_id_out_of_range"
	// CodeParseDefaultCanIDOutOfRange — default CAN ID literal exceeds 29-bit range.
	CodeParseDefaultCanIDOutOfRange = "parse_default_can_id_out_of_range"
	// CodeParseInvalidDLCBytes — DLC byte count is not a valid CAN/CAN-FD value.
	CodeParseInvalidDLCBytes = "parse_invalid_dlc_bytes"
	// CodeParseRootNotObject — JSON root is not an object.
	CodeParseRootNotObject = "parse_root_not_object"
	// CodeParseMissingSignalName — required `name` field absent on a signal.
	CodeParseMissingSignalName = "parse_missing_signal_name"
	// CodeParseSignalBitLengthZero — signal has zero bit length.
	CodeParseSignalBitLengthZero = "parse_signal_bit_length_zero"
	// CodeParseSignalStartBitExceedsFrame — signal start bit lies outside the message's frame capacity.
	CodeParseSignalStartBitExceedsFrame = "parse_signal_start_bit_exceeds_frame"
	// CodeParseSignalBitLengthExceedsFrame — signal bit length exceeds the message's frame capacity.
	CodeParseSignalBitLengthExceedsFrame = "parse_signal_bit_length_exceeds_frame"
	// CodeParseSignalBigEndianOverflow — big-endian signal's descending bit run extends past the end of the frame.
	CodeParseSignalBigEndianOverflow = "parse_signal_big_endian_overflow"
	// CodeParseInvalidKind — kind tag not recognized.
	CodeParseInvalidKind = "parse_invalid_kind"
	// CodeParseNonTerminatingRational — rational value lacks a terminating decimal representation.
	CodeParseNonTerminatingRational = "parse_non_terminating_rational"
	// CodeParseInvalidIdentifier — identifier fails DBC's identifier syntax.
	CodeParseInvalidIdentifier = "parse_invalid_identifier"
	// CodeParseNonIntegerMultiplexValue — `multiplex_values` array contains a non-natural element.
	CodeParseNonIntegerMultiplexValue = "parse_non_integer_multiplex_value"
	// CodeParseNonNaturalField — a field is present but its value is not a JSON natural number.
	CodeParseNonNaturalField = "parse_non_natural_field"

	// CodeDBCTextParseFailure — generic .dbc text parse failure.
	CodeDBCTextParseFailure = "dbc_text_parse_failure"
	// CodeDBCTextTrailingInput — .dbc text contains unparsed trailing characters.
	CodeDBCTextTrailingInput = "dbc_text_trailing_input"
	// CodeDBCTextAttributeRefinementFailed — BA_ value fails its BA_DEF_ refinement.
	CodeDBCTextAttributeRefinementFailed = "dbc_text_attribute_refinement_failed"

	// CodeFrameSignalNotFound — frame-level: signal name not declared on the message.
	CodeFrameSignalNotFound = "frame_signal_not_found"
	// CodeFrameSignalIndexOOB — frame-level: signal index out of range for the message.
	CodeFrameSignalIndexOOB = "frame_signal_index_oob"
	// CodeFrameInjectionFailed — bit-injection of a signal value failed.
	// Common causes: physical value outside the signal's [min, max] range,
	// computed raw value not fitting the signal's bit width, or scale/offset
	// reverse-transform producing a non-integer where the signal is unsigned.
	CodeFrameInjectionFailed = "frame_injection_failed"
	// CodeFrameSignalsOverlap — two signals occupy overlapping bit positions.
	CodeFrameSignalsOverlap = "frame_signals_overlap"
	// CodeFrameCanIDNotFound — no message in the DBC has this CAN ID.
	CodeFrameCanIDNotFound = "frame_can_id_not_found"
	// CodeFrameCanIDMismatch — frame CAN ID disagrees with the message ID resolved by name.
	CodeFrameCanIDMismatch = "frame_can_id_mismatch"
	// CodeFrameSignalValueOutOfBounds — physical value outside [min, max] bounds.
	CodeFrameSignalValueOutOfBounds = "frame_signal_value_out_of_bounds"

	// CodeInputBoundExceeded is any input bound crossed at any parser
	// surface; the payload's bound_kind field says which.
	CodeInputBoundExceeded = "input_bound_exceeded"

	// CodeRouteMissingField — required field absent on a routed request.
	CodeRouteMissingField = "route_missing_field"
	// CodeRouteMissingArray — expected array field absent on a routed request.
	CodeRouteMissingArray = "route_missing_array"
	// CodeRouteUnknownCommand — command name not recognized by the dispatcher.
	CodeRouteUnknownCommand = "route_unknown_command"
	// CodeRouteMissingCommandField — request body missing the `cmd` field.
	CodeRouteMissingCommandField = "route_missing_command_field"
	// CodeRouteDLCExceedsMax — DLC value exceeds the maximum allowed.
	CodeRouteDLCExceedsMax = "route_dlc_exceeds_max"
	// CodeRouteByteArrayParseFailed — byte-array body could not be parsed.
	CodeRouteByteArrayParseFailed = "route_byte_array_parse_failed"
	// CodeRouteByteCountMismatch — byte count does not match DLC.
	CodeRouteByteCountMismatch = "route_byte_count_mismatch"
	// CodeRouteMissingDBCField — `dbc` field absent on a request that requires it.
	CodeRouteMissingDBCField = "route_missing_dbc_field"
	// CodeRouteMissingPropsField — `properties` field absent on a request that requires it.
	CodeRouteMissingPropsField = "route_missing_props_field"

	// CodeHandlerNoDBC — handler invoked before any DBC was parsed.
	CodeHandlerNoDBC = "handler_no_dbc"
	// CodeHandlerAlreadyStreaming — start_stream called while a stream is active.
	CodeHandlerAlreadyStreaming = "handler_already_streaming"
	// CodeHandlerNotStreaming — frame-stream operation invoked outside a stream.
	CodeHandlerNotStreaming = "handler_not_streaming"
	// CodeHandlerStreamNotStarted — operation requires start_stream first.
	CodeHandlerStreamNotStarted = "handler_stream_not_started"
	// CodeHandlerStreamActive — operation cannot be performed while a stream is active.
	CodeHandlerStreamActive = "handler_stream_active"
	// CodeHandlerPropertyParseFailed — set_properties body could not be parsed.
	CodeHandlerPropertyParseFailed = "handler_property_parse_failed"
	// CodeHandlerInvalidDLCCode — DLC code outside [0, 15].
	CodeHandlerInvalidDLCCode = "handler_invalid_dlc_code"
	// CodeHandlerValidationFailed — handler-level validation rejected the request.
	CodeHandlerValidationFailed = "handler_validation_failed"
	// CodeHandlerTextRoundtripFailed — FormatDBCText refused: emitted text does not re-parse to the input DBC.
	CodeHandlerTextRoundtripFailed = "handler_text_roundtrip_failed"
	// CodeHandlerNonMonotonicTimestamp — frame timestamp regressed relative to the previous frame.
	CodeHandlerNonMonotonicTimestamp = "handler_non_monotonic_timestamp"

	// CodeDispatchMissingTypeField — request object missing the `type` field.
	CodeDispatchMissingTypeField = "dispatch_missing_type_field"
	// CodeDispatchUnknownMessageType — `type` value not recognized.
	CodeDispatchUnknownMessageType = "dispatch_unknown_message_type"
	// CodeDispatchInvalidJSON — request body is not valid JSON.
	CodeDispatchInvalidJSON = "dispatch_invalid_json"
	// CodeDispatchRequestNotObject — request body is not a JSON object at root.
	CodeDispatchRequestNotObject = "dispatch_request_not_object"

	// CodeExtractionMuxValueMismatch — multiplexor value does not match the requested signal's mux selector.
	CodeExtractionMuxValueMismatch = "extraction_mux_value_mismatch"
	// CodeExtractionMuxSignalNotFound — multiplexor signal referenced by a muxed signal is missing.
	CodeExtractionMuxSignalNotFound = "extraction_mux_signal_not_found"
	// CodeExtractionMuxChainCycle — multiplexor chain references itself.
	CodeExtractionMuxChainCycle = "extraction_mux_chain_cycle"
	// CodeExtractionMuxExtractionFailed — multiplexor extraction step failed.
	CodeExtractionMuxExtractionFailed = "extraction_mux_extraction_failed"
	// CodeExtractionBitExtractionFailed — bit-extraction step failed (out-of-range / scaling error).
	CodeExtractionBitExtractionFailed = "extraction_bit_extraction_failed"
	// CodeExtractionValueExceedsWireRange — the extracted exact value's reduced
	// numerator or denominator exceeds the signed 64-bit binary-wire range.
	CodeExtractionValueExceedsWireRange = "extraction_value_exceeds_wire_range"
)

// newError builds a typed *Error without a wire code or inner cause.
func newError(kind ErrorKind, msg string) *Error {
	return &Error{Kind: kind, Message: msg}
}

// newCodedError builds a typed *Error carrying an Agda-side Code (one
// of the Code* constants above) so callers can discriminate cleanly
// with errors.Is / matching on Code.
func newCodedError(kind ErrorKind, code, msg string) *Error {
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

// InputBoundExceededError reports an input bound the kernel refused, with
// the bound, what was observed and the limit. It is the kernel's
// InputBoundExceeded, and the peer bindings carry the same type: Python's
// InputBoundExceededError, the C++ aletheia::InputBoundExceededError and
// the Rust Error::InputBoundExceeded.
//
// Use [errors.As] to inspect:
//
//	var bex *aletheia.InputBoundExceededError
//	if errors.As(err, &bex) {
//		log.Printf("rejected %s = %d (limit %d)", bex.BoundKind, bex.Observed, bex.Limit)
//	}
type InputBoundExceededError struct {
	// BoundKind names the bound, one of the BoundKind constants in limits.go.
	BoundKind string
	// Observed is the input value that exceeded the limit.
	Observed uint64
	// Limit is the bound itself, which limits.go mirrors from the kernel.
	Limit uint64
	// Code is the wire error code, always [CodeInputBoundExceeded]: the
	// decoder lifts this type for no other.
	Code string
}

// Error implements the error interface.
func (e *InputBoundExceededError) Error() string {
	return fmt.Sprintf("aletheia validation error: %s %d exceeds limit %d",
		e.BoundKind, e.Observed, e.Limit)
}

// newInputBoundExceededError builds the typed error, for the lifter in
// json.go and for the bounds the binding checks before the call.
func newInputBoundExceededError(kind string, observed, limit uint64, code string) *InputBoundExceededError {
	return &InputBoundExceededError{
		BoundKind: kind,
		Observed:  observed,
		Limit:     limit,
		Code:      code,
	}
}

// ValidationFailedError reports a DBC that parsed but failed structural
// validation with at least one error-severity issue, as [Client.ParseDBC]
// and [Client.ParseDBCText] refuse it. The issues have the element shape
// of a validation response. Python raises DBCValidationFailedError and
// Rust returns Error::ValidationFailed for the same refusal; C++ carries
// it on its one error class, under ErrorCode::HandlerValidationFailed.
//
// Use [errors.As] to inspect:
//
//	var vfe *aletheia.ValidationFailedError
//	if errors.As(err, &vfe) {
//		for _, issue := range vfe.Issues {
//			log.Printf("[%s] %s: %s", issue.Severity, issue.Code, issue.Detail)
//		}
//	}
type ValidationFailedError struct {
	// Issues are the structural validation findings in wire order,
	// with the same element shape as [ValidationResult].Issues.
	Issues []ValidationIssue
	// HasErrors reports whether any issue has error severity; it is read
	// from the wire rather than assumed, though the kernel sets it here.
	HasErrors bool
	// Code is the wire error code, always [CodeHandlerValidationFailed]:
	// the decoder lifts this type for no other.
	Code string
	// Message is the envelope's human-readable diagnostic.
	Message string
}

// Error renders exactly as a generic coded protocol error with the same
// message, so a caller that only prints it sees one shape.
func (e *ValidationFailedError) Error() string {
	return fmt.Sprintf("aletheia %s error: %s", ErrProtocol, e.Message)
}

// newValidationFailedError builds the typed error from a decoded envelope,
// for validationFailedFromResponse in json.go.
func newValidationFailedError(issues []ValidationIssue, hasErrors bool, code, msg string) *ValidationFailedError {
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
// Use [errors.As] to inspect:
//
//	var trte *aletheia.TextRoundTripFailedError
//	if errors.As(err, &trte) {
//		for _, issue := range trte.Issues {
//			log.Printf("[%s] %s: %s", issue.Severity, issue.Code, issue.Detail)
//		}
//	}
type TextRoundTripFailedError struct {
	// Issues are the round-trip diagnostics in wire order, led by the
	// error-severity text_roundtrip_divergence issue.
	Issues []ValidationIssue
	// HasErrors reports whether any issue has error severity; it is read
	// from the wire rather than assumed.
	HasErrors bool
	// Code is the wire error code, always [CodeHandlerTextRoundtripFailed]:
	// the decoder lifts this type for no other.
	Code string
	// Message is the envelope's human-readable diagnostic.
	Message string
}

// Error renders exactly as a generic coded protocol error with the same
// message, as [ValidationFailedError.Error] does.
func (e *TextRoundTripFailedError) Error() string {
	return fmt.Sprintf("aletheia %s error: %s", ErrProtocol, e.Message)
}

// newTextRoundTripFailedError builds the typed error from a decoded
// envelope, for textRoundtripFailedFromResponse in json.go.
func newTextRoundTripFailedError(issues []ValidationIssue, hasErrors bool, code, msg string) *TextRoundTripFailedError {
	return &TextRoundTripFailedError{
		Issues:    issues,
		HasErrors: hasErrors,
		Code:      code,
		Message:   msg,
	}
}
