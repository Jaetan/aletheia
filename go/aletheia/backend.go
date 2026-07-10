// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

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
//
// # Thread safety contract
//
// Implementations MAY assume the caller serialises all method
// invocations against a single backend instance.  [Client] provides
// this serialisation via an internal token channel (see
// `client.go::lockCh`); direct callers (test harnesses, custom
// orchestrators that bypass [Client]) MUST provide equivalent
// serialisation.
//
// [MockBackend] enforces serialisation defensively via an internal
// `sync.Mutex`; [FFIBackend] does NOT carry a mutex — its
// thread-unsafety is intentional because GHC RTS state has process-
// global ownership, and double-locking would only mask caller-side
// bugs.  Concurrent direct calls to [FFIBackend] are undefined
// behaviour at the GHC RTS level (StablePtr accounting + StreamState
// IORef updates race).
//
// The method set is grouped by data-format and direction to document the
// JSON-command / binary-FFI mix.  The grouping
// mirrors the [MANDATORY] / [OPTIONAL] split on C++ `IBackend` at
// `cpp/include/aletheia/backend.hpp`; Go interfaces have no default-method
// machinery, so every method is technically mandatory at the type level,
// but the surface separates cleanly into three layers:
//
//  1. Session lifecycle + JSON command bus.  Every backend must minimally
//     answer here; the JSON command path is the cross-binding semantic
//     ground truth and remains the fallback for endpoints a backend chooses
//     not to specialise (the Mock implements per-method canned responses
//     instead of routing through `Process`).
//  2. Binary-FFI send / event / state-transition endpoints.  Binary input
//     bypasses JSON deserialisation on the send side; the response remains
//     a JSON string.  These are the per-frame hot path.
//  3. Binary-FFI bidirectional endpoints.  Raw payload bytes on both input
//     and output sides.  No JSON allocation per call.
type Backend interface {
	backend() // sealed — prevents third-party implementations

	// ─── Group 1: Session lifecycle + JSON command bus ────────────────────

	// Init creates a new session and returns an opaque state handle.
	Init() (unsafe.Pointer, error)
	// Process sends a JSON command and returns the JSON response.
	Process(state unsafe.Pointer, input string) (string, error)
	// Close finalizes and frees the session state.
	Close(state unsafe.Pointer)

	// ─── Group 2: Binary-FFI send / event / state-transition endpoints ────
	// Binary input → JSON response.

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

	// ─── Group 3: Binary-FFI bidirectional endpoints ──────────────────────
	// Raw payload bytes on both input and output — no JSON allocation.

	// BuildFrameBin builds a CAN frame returning raw payload bytes, bypassing JSON on both input and output.
	BuildFrameBin(state unsafe.Pointer, id CANID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error)
	// UpdateFrameBin updates a CAN frame returning raw payload bytes, bypassing JSON on both input and output.
	UpdateFrameBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error)
	// ExtractSignalsBin extracts signals returning packed binary (no JSON on output).
	// Returns the raw binary buffer that the caller must parse.
	ExtractSignalsBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte) ([]byte, error)
}
