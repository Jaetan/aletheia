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
	// SendErrorBinary sends a CAN error event (no ID, no payload).
	// Error frames are acknowledged without LTL evaluation.
	SendErrorBinary(state unsafe.Pointer, ts Timestamp) (string, error)
	// SendRemoteBinary sends a CAN remote frame event (ID but no payload).
	// Remote frames are acknowledged without LTL evaluation.
	SendRemoteBinary(state unsafe.Pointer, ts Timestamp, id CanID) (string, error)
	// StartStreamBinary begins streaming mode without JSON parsing on input.
	StartStreamBinary(state unsafe.Pointer) (string, error)
	// EndStreamBinary finalizes streaming and returns verdicts without JSON parsing on input.
	EndStreamBinary(state unsafe.Pointer) (string, error)
	// FormatDbcBinary returns the loaded DBC as JSON without JSON parsing on input.
	FormatDbcBinary(state unsafe.Pointer) (string, error)
	// ExtractSignalsBinary extracts signals from a binary CAN frame without JSON parsing on input.
	ExtractSignalsBinary(state unsafe.Pointer, id CanID, dlc DLC, data []byte) (string, error)
	// BuildFrameBinary builds a CAN frame from signal index-value pairs without JSON parsing on input.
	// indices are 0-based positions in the DBC message's signal list.
	// nums and dens are parallel arrays of rational numerator/denominator pairs.
	BuildFrameBinary(state unsafe.Pointer, id CanID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) (string, error)
	// UpdateFrameBinary updates signals in a CAN frame by index without JSON parsing on input.
	// indices are 0-based positions in the DBC message's signal list.
	// nums and dens are parallel arrays of rational numerator/denominator pairs.
	UpdateFrameBinary(state unsafe.Pointer, id CanID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) (string, error)
	// BuildFrameBin builds a CAN frame returning raw payload bytes, bypassing JSON on both input and output.
	BuildFrameBin(state unsafe.Pointer, id CanID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error)
	// UpdateFrameBin updates a CAN frame returning raw payload bytes, bypassing JSON on both input and output.
	UpdateFrameBin(state unsafe.Pointer, id CanID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error)
	// ExtractSignalsBin extracts signals returning packed binary (no JSON on output).
	// Returns the raw binary buffer that the caller must parse.
	ExtractSignalsBin(state unsafe.Pointer, id CanID, dlc DLC, data []byte) ([]byte, error)
	// Close finalizes and frees the session state.
	Close(state unsafe.Pointer)
}
