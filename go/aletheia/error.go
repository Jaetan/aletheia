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
type Error struct {
	Kind    ErrorKind
	Message string
}

func (e *Error) Error() string {
	return fmt.Sprintf("aletheia %s error: %s", e.Kind, e.Message)
}

func newError(kind ErrorKind, msg string) *Error {
	return &Error{Kind: kind, Message: msg}
}

func protocolError(msg string) *Error   { return newError(ErrProtocol, msg) }
func validationError(msg string) *Error { return newError(ErrValidation, msg) }
func stateError(msg string) *Error      { return newError(ErrState, msg) }
func ffiError(msg string) *Error        { return newError(ErrFFI, msg) }
