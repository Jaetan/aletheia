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

const (
	// ErrProtocol indicates a JSON parsing or protocol mismatch with the Agda core.
	ErrProtocol ErrorKind = iota
	// ErrValidation indicates a structural issue in the DBC definition.
	ErrValidation
	// ErrState indicates an operation was attempted in the wrong client state.
	ErrState
	// ErrFFI indicates a failure in the FFI layer (dlopen, dlsym, hs_init).
	ErrFFI
)

// String returns the lowercase name of the error kind.
func (k ErrorKind) String() string {
	switch k {
	case ErrProtocol:
		return "protocol"
	case ErrValidation:
		return "validation"
	case ErrState:
		return "state"
	case ErrFFI:
		return "ffi"
	default:
		return "unknown"
	}
}

// Error is the error type returned by all Aletheia operations.
// Use [errors.As] to inspect the [ErrorKind], and [errors.Unwrap] to
// retrieve the underlying cause (if any).
type Error struct {
	Kind    ErrorKind
	Code    string // Machine-readable error code from Agda (empty for client-side errors)
	Message string
	Cause   error // optional wrapped cause; nil when there is no underlying error
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

// Machine-readable error codes matching Agda Error ADT (50 codes).
// Each maps 1:1 to an Agda error constructor via errorCode.
const (
	// Parse errors.
	CodeParseMissingField            = "parse_missing_field"
	CodeParseInvalidByteOrder        = "parse_invalid_byte_order"
	CodeParseInvalidPresence         = "parse_invalid_presence"
	CodeParseMissingSigned           = "parse_missing_signed"
	CodeParseInvalidSigned           = "parse_invalid_signed"
	CodeParseNotAnObject             = "parse_not_an_object"
	CodeParseExtCanIDOutOfRange      = "parse_ext_can_id_out_of_range"
	CodeParseStdCanIDOutOfRange      = "parse_std_can_id_out_of_range"
	CodeParseDefaultCanIDOutOfRange  = "parse_default_can_id_out_of_range"
	CodeParseInvalidDLCBytes         = "parse_invalid_dlc_bytes"
	CodeParseRootNotObject           = "parse_root_not_object"
	CodeParseMissingSignalName       = "parse_missing_signal_name"
	CodeParseSignalBitLengthZero     = "parse_signal_bit_length_zero"
	CodeParseSignalOverflowsFrame    = "parse_signal_overflows_frame"
	CodeParseSignalMSBBelowBitLength = "parse_signal_msb_below_bit_length"
	CodeParseInvalidKind             = "parse_invalid_kind"
	// Frame errors.
	CodeFrameSignalNotFound         = "frame_signal_not_found"
	CodeFrameSignalIndexOOB         = "frame_signal_index_oob"
	CodeFrameInjectionFailed        = "frame_injection_failed"
	CodeFrameSignalsOverlap         = "frame_signals_overlap"
	CodeFrameCanIDNotFound          = "frame_can_id_not_found"
	CodeFrameCanIDMismatch          = "frame_can_id_mismatch"
	CodeFrameSignalValueOutOfBounds = "frame_signal_value_out_of_bounds"
	// Route errors.
	CodeRouteMissingField         = "route_missing_field"
	CodeRouteMissingArray         = "route_missing_array"
	CodeRouteUnknownCommand       = "route_unknown_command"
	CodeRouteMissingCommandField  = "route_missing_command_field"
	CodeRouteDLCExceedsMax        = "route_dlc_exceeds_max"
	CodeRouteByteArrayParseFailed = "route_byte_array_parse_failed"
	CodeRouteByteCountMismatch    = "route_byte_count_mismatch"
	CodeRouteMissingDBCField      = "route_missing_dbc_field"
	CodeRouteMissingPropsField    = "route_missing_props_field"
	// Handler errors.
	CodeHandlerNoDBC                 = "handler_no_dbc"
	CodeHandlerAlreadyStreaming      = "handler_already_streaming"
	CodeHandlerNotStreaming          = "handler_not_streaming"
	CodeHandlerStreamNotStarted      = "handler_stream_not_started"
	CodeHandlerStreamActive          = "handler_stream_active"
	CodeHandlerPropertyParseFailed   = "handler_property_parse_failed"
	CodeHandlerInvalidDLCCode        = "handler_invalid_dlc_code"
	CodeHandlerValidationFailed      = "handler_validation_failed"
	CodeHandlerNonMonotonicTimestamp = "handler_non_monotonic_timestamp"
	// Dispatch errors.
	CodeDispatchMissingTypeField   = "dispatch_missing_type_field"
	CodeDispatchUnknownMessageType = "dispatch_unknown_message_type"
	CodeDispatchInvalidJSON        = "dispatch_invalid_json"
	CodeDispatchRequestNotObject   = "dispatch_request_not_object"
	// Extraction errors.
	CodeExtractionMuxValueMismatch    = "extraction_mux_value_mismatch"
	CodeExtractionMuxSignalNotFound   = "extraction_mux_signal_not_found"
	CodeExtractionMuxChainCycle       = "extraction_mux_chain_cycle"
	CodeExtractionMuxExtractionFailed = "extraction_mux_extraction_failed"
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
