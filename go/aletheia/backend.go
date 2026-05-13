package aletheia

import (
	"log/slog"
	"unsafe"
)

// FFIBackendOption configures optional [FFIBackend] behavior.
type FFIBackendOption func(*ffiConfig)

type ffiConfig struct {
	rtsCores int
	logger   *slog.Logger
}

// WithRTSCores sets the number of GHC RTS capabilities (-N flag).
// Use 1 (default) for single-bus monitoring. Set to the number of CAN
// buses for multi-bus monitoring from separate goroutines. Only takes
// effect on the first [NewFFIBackend] call in a process.
func WithRTSCores(n int) FFIBackendOption {
	return func(c *ffiConfig) { c.rtsCores = n }
}

// WithFFILogger sets a logger for FFI backend initialization events.
// When nil (default), no logging occurs.
func WithFFILogger(l *slog.Logger) FFIBackendOption {
	return func(c *ffiConfig) { c.logger = l }
}

// Backend abstracts the FFI boundary to the Agda core.
// Production code uses [FFIBackend]; tests use [MockBackend].
// Sealed: only types in this package may implement Backend.
type Backend interface {
	backend() // sealed — prevents third-party implementations
	// Init creates a new session and returns an opaque state handle.
	Init() (unsafe.Pointer, error)
	// Process sends a JSON command and returns the JSON response.
	Process(state unsafe.Pointer, input string) (string, error)
	// SendFrameBinary sends a CAN frame via the binary FFI, bypassing JSON
	// serialization on the input side. Returns the JSON response string.
	// CAN-FD BRS / ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) are
	// passed as *bool — pass nil for CAN 2.0B frames where the bits do
	// not exist.  The Agda core does not consume BRS / ESI; they are
	// pass-through metadata for binding consumers.
	// Precondition: ts.Microseconds >= 0 (enforced by [Client.SendFrame]).
	SendFrameBinary(
		state unsafe.Pointer, ts Timestamp,
		id CANID, dlc DLC, data []byte,
		brs *bool, esi *bool,
	) (string, error)
	// SendErrorBinary sends a CAN error event (no ID, no payload).
	// Error frames are acknowledged without LTL evaluation.
	// Precondition: ts.Microseconds >= 0 (enforced by [Client.SendError]
	// but not checked at the Backend level for direct callers).
	SendErrorBinary(state unsafe.Pointer, ts Timestamp) (string, error)
	// SendRemoteBinary sends a CAN remote frame event (ID but no payload).
	// Remote frames are acknowledged without LTL evaluation.
	// Precondition: ts.Microseconds >= 0 (enforced by [Client.SendRemote]
	// but not checked at the Backend level for direct callers).
	SendRemoteBinary(state unsafe.Pointer, ts Timestamp, id CANID) (string, error)
	// StartStreamBinary begins streaming mode without JSON parsing on input.
	StartStreamBinary(state unsafe.Pointer) (string, error)
	// EndStreamBinary finalizes streaming and returns verdicts without JSON parsing on input.
	EndStreamBinary(state unsafe.Pointer) (string, error)
	// FormatDBCBinary returns the loaded DBC as JSON without JSON parsing on input.
	FormatDBCBinary(state unsafe.Pointer) (string, error)
	// ExtractSignalsBinary extracts signals from a binary CAN frame without JSON parsing on input.
	ExtractSignalsBinary(state unsafe.Pointer, id CANID, dlc DLC, data []byte) (string, error)
	// BuildFrameBin builds a CAN frame returning raw payload bytes, bypassing JSON on both input and output.
	BuildFrameBin(state unsafe.Pointer, id CANID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error)
	// UpdateFrameBin updates a CAN frame returning raw payload bytes, bypassing JSON on both input and output.
	UpdateFrameBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error)
	// ExtractSignalsBin extracts signals returning packed binary (no JSON on output).
	// Returns the raw binary buffer that the caller must parse.
	ExtractSignalsBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte) ([]byte, error)
	// Close finalizes and frees the session state.
	Close(state unsafe.Pointer)
}
