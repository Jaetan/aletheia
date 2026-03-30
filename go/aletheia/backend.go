package aletheia

import "unsafe"

// FFIBackendOption configures optional [FFIBackend] behavior.
type FFIBackendOption func(*ffiConfig)

type ffiConfig struct {
	rtsCores int
}

// WithRTSCores sets the number of GHC RTS capabilities (-N flag).
// Use 1 (default) for single-bus monitoring. Set to the number of CAN
// buses for multi-bus monitoring from separate goroutines. Only takes
// effect on the first [NewFFIBackend] call in a process.
func WithRTSCores(n int) FFIBackendOption {
	return func(c *ffiConfig) { c.rtsCores = n }
}

// Backend abstracts the FFI boundary to the Agda core.
// Production code uses [FFIBackend]; tests use [MockBackend].
type Backend interface {
	// Init creates a new session and returns an opaque state handle.
	Init() (unsafe.Pointer, error)
	// Process sends a JSON command and returns the JSON response.
	Process(state unsafe.Pointer, input string) (string, error)
	// SendFrameBinary sends a CAN frame via the binary FFI, bypassing JSON
	// serialization on the input side. Returns the JSON response string.
	// Precondition: ts.Microseconds >= 0 (enforced by [Client.SendFrame]).
	SendFrameBinary(state unsafe.Pointer, ts Timestamp, id CanID, dlc DLC, data []byte) (string, error)
	// Close finalizes and frees the session state.
	Close(state unsafe.Pointer)
}
