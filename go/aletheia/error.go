package aletheia

import "fmt"

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

// Machine-readable error codes matching Agda Error ADT (37 codes).
// Each maps 1:1 to an Agda error constructor via errorCode.
const (
	// Parse errors.
	CodeParseMissingField          = "parse_missing_field"
	CodeParseInvalidByteOrder      = "parse_invalid_byte_order"
	CodeParseInvalidPresence       = "parse_invalid_presence"
	CodeParseMissingSigned         = "parse_missing_signed"
	CodeParseInvalidSigned         = "parse_invalid_signed"
	CodeParseNotAnObject           = "parse_not_an_object"
	CodeParseExtCanIDOutOfRange    = "parse_ext_can_id_out_of_range"
	CodeParseStdCanIDOutOfRange    = "parse_std_can_id_out_of_range"
	CodeParseDefaultCanIDOutOfRange = "parse_default_can_id_out_of_range"
	CodeParseInvalidDLCBytes       = "parse_invalid_dlc_bytes"
	CodeParseRootNotObject         = "parse_root_not_object"
	CodeParseMissingSignalName     = "parse_missing_signal_name"
	// Frame errors.
	CodeFrameSignalNotFound  = "frame_signal_not_found"
	CodeFrameSignalIndexOOB  = "frame_signal_index_oob"
	CodeFrameInjectionFailed = "frame_injection_failed"
	CodeFrameSignalsOverlap  = "frame_signals_overlap"
	CodeFrameCanIDNotFound   = "frame_can_id_not_found"
	CodeFrameCanIDMismatch   = "frame_can_id_mismatch"
	// Route errors.
	CodeRouteMissingField        = "route_missing_field"
	CodeRouteMissingArray        = "route_missing_array"
	CodeRouteUnknownCommand      = "route_unknown_command"
	CodeRouteMissingCommandField = "route_missing_command_field"
	CodeRouteDLCExceedsMax       = "route_dlc_exceeds_max"
	CodeRouteByteArrayParseFailed = "route_byte_array_parse_failed"
	CodeRouteByteCountMismatch   = "route_byte_count_mismatch"
	CodeRouteMissingDBCField     = "route_missing_dbc_field"
	CodeRouteMissingPropsField   = "route_missing_props_field"
	// Handler errors.
	CodeHandlerNoDBC                = "handler_no_dbc"
	CodeHandlerAlreadyStreaming      = "handler_already_streaming"
	CodeHandlerNotStreaming          = "handler_not_streaming"
	CodeHandlerStreamNotStarted     = "handler_stream_not_started"
	CodeHandlerStreamActive         = "handler_stream_active"
	CodeHandlerSignalListParseFailed = "handler_signal_list_parse_failed"
	CodeHandlerPropertyParseFailed  = "handler_property_parse_failed"
	CodeHandlerInvalidDLCCode       = "handler_invalid_dlc_code"
	CodeHandlerValidationFailed     = "handler_validation_failed"
	// Dispatch errors.
	CodeDispatchMissingTypeField  = "dispatch_missing_type_field"
	CodeDispatchUnknownMessageType = "dispatch_unknown_message_type"
	CodeDispatchInvalidJSON       = "dispatch_invalid_json"
	CodeDispatchRequestNotObject  = "dispatch_request_not_object"
)

func newError(kind ErrorKind, msg string) *Error {
	return &Error{Kind: kind, Message: msg}
}

func newCodedError(kind ErrorKind, code, msg string) *Error {
	return &Error{Kind: kind, Code: code, Message: msg}
}

func wrapError(kind ErrorKind, msg string, cause error) *Error {
	return &Error{Kind: kind, Message: msg, Cause: cause}
}

func protocolError(msg string) *Error             { return newError(ErrProtocol, msg) }
func validationError(msg string) *Error           { return newError(ErrValidation, msg) }
func stateError(msg string) *Error                { return newError(ErrState, msg) }
func ffiError(msg string) *Error                  { return newError(ErrFFI, msg) }
func wrapProtocol(msg string, cause error) *Error { return wrapError(ErrProtocol, msg, cause) }
