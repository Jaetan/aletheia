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

func newError(kind ErrorKind, msg string) *Error {
	return &Error{Kind: kind, Message: msg}
}

func wrapError(kind ErrorKind, msg string, cause error) *Error {
	return &Error{Kind: kind, Message: msg, Cause: cause}
}

func protocolError(msg string) *Error             { return newError(ErrProtocol, msg) }
func validationError(msg string) *Error           { return newError(ErrValidation, msg) }
func stateError(msg string) *Error                { return newError(ErrState, msg) }
func ffiError(msg string) *Error                  { return newError(ErrFFI, msg) }
func wrapProtocol(msg string, cause error) *Error { return wrapError(ErrProtocol, msg, cause) }
