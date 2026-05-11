package aletheia

import (
	"errors"
	"fmt"
)

// ErrBinaryPathUnsupported is returned by a Backend whose concrete
// implementation cannot service the binary extraction path (e.g.
// MockBackend has no real FFI to call aletheia_extract_signals_bin).
// Client.ExtractSignals falls through to the JSON path ONLY on this
// sentinel — any other error from ExtractSignalsBin propagates.
var ErrBinaryPathUnsupported = errors.New("binary path not supported by this backend")

// ErrorKind classifies the source of an error.
type ErrorKind int

//go:generate stringer -type=ErrorKind -linecomment -output=errorkind_string.go

const (
	// ErrProtocol indicates a JSON parsing or protocol mismatch with the Agda core.
	ErrProtocol ErrorKind = iota // protocol
	// ErrValidation indicates a structural issue in the DBC definition.
	ErrValidation // validation
	// ErrState indicates an operation was attempted in the wrong client state.
	ErrState // state
	// ErrFFI indicates a failure in the FFI layer (dlopen, dlsym, hs_init).
	ErrFFI // ffi
)

// Error is the error type returned by all Aletheia operations.
// Use [errors.As] to inspect the [ErrorKind], and [errors.Unwrap] to
// retrieve the underlying cause (if any).
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

// Error returns a human-readable string in the form "aletheia <kind> error: <message>".
func (e *Error) Error() string {
	if e.Cause != nil {
		return fmt.Sprintf("aletheia %s error: %s: %s", e.Kind, e.Message, e.Cause)
	}
	return fmt.Sprintf("aletheia %s error: %s", e.Kind, e.Message)
}

// Unwrap returns the underlying error, enabling [errors.Is] and [errors.As].
func (e *Error) Unwrap() error { return e.Cause }

// Machine-readable error codes matching Agda Error ADT (51 codes).
// Each maps 1:1 to an Agda error constructor via errorCode.
//
// Constants below are organized into eight groups (Parse / DBC text /
// Frame / Route / Handler / Dispatch / Extraction); the wire string
// (snake_case suffix on each constant) is the canonical identifier used
// by the structured-log + Error.Code surface.  See [Error.Code] and
// [docs/architecture/PROTOCOL.md] for the full Agda ADT mapping.
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
	// CodeParseSignalOverflowsFrame — signal bit range extends beyond frame DLC.
	CodeParseSignalOverflowsFrame = "parse_signal_overflows_frame"
	// CodeParseSignalMSBBelowBitLength — signal MSB is less than its declared bit length.
	CodeParseSignalMSBBelowBitLength = "parse_signal_msb_below_bit_length"
	// CodeParseInvalidKind — kind tag not recognized.
	CodeParseInvalidKind = "parse_invalid_kind"
	// CodeParseNonTerminatingRational — rational value lacks a terminating decimal representation.
	CodeParseNonTerminatingRational = "parse_non_terminating_rational"
	// CodeParseInvalidIdentifier — identifier fails DBC's identifier syntax.
	CodeParseInvalidIdentifier = "parse_invalid_identifier"

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
	CodeFrameInjectionFailed = "frame_injection_failed"
	// CodeFrameSignalsOverlap — two signals occupy overlapping bit positions.
	CodeFrameSignalsOverlap = "frame_signals_overlap"
	// CodeFrameCanIDNotFound — no message in the DBC has this CAN ID.
	CodeFrameCanIDNotFound = "frame_can_id_not_found"
	// CodeFrameCanIDMismatch — frame CAN ID disagrees with the message ID resolved by name.
	CodeFrameCanIDMismatch = "frame_can_id_mismatch"
	// CodeFrameSignalValueOutOfBounds — physical value outside [min, max] bounds.
	CodeFrameSignalValueOutOfBounds = "frame_signal_value_out_of_bounds"

	// CodeInputBoundExceeded — adversarial-input bound exceeded at any
	// parser surface.  Consolidated from the previously per-ADT codes
	// `parse_input_bound_exceeded` / `frame_input_bound_exceeded` /
	// `dbc_text_input_bound_exceeded` (R19 cluster 14 / AGDA-C-6.2,
	// 2026-05-11).  Discriminate which bound was crossed by the
	// `bound_kind` field carried in the structured payload.
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

// wrapProtocol is the wrap variant of protocolError for JSON decode / I/O failures.
func wrapProtocol(msg string, cause error) *Error { return wrapError(ErrProtocol, msg, cause) }

// wrapValidation is the wrap variant of validationError for nested parse failures.
func wrapValidation(msg string, cause error) *Error { return wrapError(ErrValidation, msg, cause) }

// NewValidationError returns an [ErrValidation] error with the given message.
// Exported so external loaders (the Excel subpackage, custom plug-ins) report
// failures with the same kind/Code shape as the built-in YAML loader.
func NewValidationError(msg string) *Error { return validationError(msg) }

// WrapValidationError wraps an underlying cause as an [ErrValidation] error
// with the given message. Kept public for the same reason as
// [NewValidationError] — external loaders should reuse this instead of
// constructing *Error directly.
func WrapValidationError(msg string, cause error) *Error {
	return wrapValidation(msg, cause)
}

// InputBoundExceededError reports an adversarial-input bound violation.
// Mirrors the Agda InputBoundExceeded constructor on
// ParseError / DBCTextParseError / FrameError, and the equivalent type
// in the Python (aletheia.InputBoundExceededError) and C++
// (aletheia::InputBoundExceededError) bindings — keep the three surfaces
// in sync per `feedback_cross_language_parity.md`.
//
// Use [errors.As] to inspect:
//
//	var bex *aletheia.InputBoundExceededError
//	if errors.As(err, &bex) {
//		log.Printf("rejected %s = %d (limit %d)", bex.BoundKind, bex.Observed, bex.Limit)
//	}
type InputBoundExceededError struct {
	// BoundKind names which kind of bound was crossed (one of the
	// BoundKind* constants in `limits.go`).
	BoundKind string
	// Observed is the input value that exceeded the limit.
	Observed uint64
	// Limit is the canonical bound from `limits.go` / Aletheia.Limits.
	Limit uint64
	// Code is the Agda wire error code.  After R19 cluster 14 /
	// AGDA-C-6.2 consolidation, this is always
	// [CodeInputBoundExceeded] ("input_bound_exceeded") for
	// adversarial-input bounds; the per-ADT codes
	// (parse_input_bound_exceeded / frame_… / dbc_text_…) were merged.
	Code string
}

// Error implements the error interface.
func (e *InputBoundExceededError) Error() string {
	return fmt.Sprintf("aletheia validation error: %s %d exceeds limit %d",
		e.BoundKind, e.Observed, e.Limit)
}

// newInputBoundExceededError constructs an InputBoundExceededError for the
// FFI-entry early-reject path (see ffi.go).
func newInputBoundExceededError(kind string, observed, limit uint64, code string) *InputBoundExceededError {
	return &InputBoundExceededError{
		BoundKind: kind,
		Observed:  observed,
		Limit:     limit,
		Code:      code,
	}
}
