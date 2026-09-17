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

// WithRTSCores sets the number of GHC RTS capabilities (the -N flag): 1, the
// default, for one bus; the number of buses when several goroutines each
// monitor their own. Only the first [NewFFIBackend] call in a process applies
// it; a later call asking for a different number logs rts.cores_mismatch.
func WithRTSCores(n int) FFIBackendOption {
	return func(c *ffiConfig) { c.rtsCores = n }
}

// WithFFILogger sets the logger for backend initialisation events. Nil, the
// default, logs nothing.
func WithFFILogger(l *slog.Logger) FFIBackendOption {
	return func(c *ffiConfig) { c.logger = l }
}

// SignalInjection is one signal's position in its message and the exact value
// to place there, as the numerator and denominator the wire carries. One slice
// of these crosses the interface where a count and three slices of that length
// used to, so the three lengths agree by construction and no boundary check
// stands in for a type. The Rust binding's backend carries the same name for
// the same thing.
type SignalInjection struct {
	// Index is the signal's position in its message's signal list.
	Index uint32
	// Numerator and Denominator are the exact value to place there.
	Numerator   int64
	Denominator int64
}

// Backend is the FFI boundary to the Agda core: [FFIBackend] in production,
// [MockBackend] in tests. It is sealed, so only this package implements it.
//
// The caller serialises every call against one backend instance. [Client]
// does so through its lockCh token channel; a direct caller (a test harness,
// an orchestrator bypassing [Client]) must do the same. [MockBackend] also
// locks internally, defensively. [FFIBackend] carries no lock on purpose: GHC
// RTS state is process-global, and a second lock would only hide a caller's
// bug. Concurrent direct calls on an [FFIBackend] race on the kernel's
// StablePtr accounting and StreamState updates.
//
// The methods fall into three groups, mirroring the [MANDATORY] and [OPTIONAL]
// split of the C++ IBackend in cpp/include/aletheia/backend.hpp; Go has no
// default methods, so every method is required here. The JSON command bus is
// the cross-binding ground truth; the binary send endpoints take binary input
// and answer JSON; the binary endpoints carry raw bytes both ways with no JSON
// allocation.
type Backend interface {
	backend() // sealed

	// Group 1: session lifecycle and the JSON command bus.

	// Init creates a session and returns its opaque state handle.
	Init() (unsafe.Pointer, error)
	// Process sends one JSON command and returns the JSON response.
	Process(state unsafe.Pointer, input string) (string, error)
	// Close finalizes and frees the session state.
	Close(state unsafe.Pointer)

	// Group 2: binary input, JSON response.

	// SendFrameBinary sends a CAN frame. The CAN-FD BRS and ESI bits
	// (ISO 11898-1:2015 §10.4.2 / §10.4.3) are nil on a CAN 2.0B frame and
	// pass through: the kernel carries them in the trace without evaluating them.
	// Precondition: ts.Microseconds >= 0, enforced by [Client.SendFrame].
	SendFrameBinary(
		state unsafe.Pointer, ts Timestamp,
		id CANID, dlc DLC, data []byte,
		brs *bool, esi *bool,
	) (string, error)
	// SendErrorBinary sends a CAN error event (no ID, no payload); error
	// frames are acknowledged without LTL evaluation.
	// Precondition: ts.Microseconds >= 0, enforced by [Client.SendError] and
	// not checked here for direct callers.
	SendErrorBinary(state unsafe.Pointer, ts Timestamp) (string, error)
	// SendRemoteBinary sends a CAN remote frame event (ID, no payload); remote
	// frames are acknowledged without LTL evaluation.
	// Precondition: ts.Microseconds >= 0, enforced by [Client.SendRemote] and
	// not checked here for direct callers.
	SendRemoteBinary(state unsafe.Pointer, ts Timestamp, id CANID) (string, error)
	// StartStreamBinary begins streaming mode.
	StartStreamBinary(state unsafe.Pointer) (string, error)
	// EndStreamBinary ends streaming mode and returns the verdicts.
	EndStreamBinary(state unsafe.Pointer) (string, error)
	// FormatDBCBinary returns the loaded DBC as JSON.
	FormatDBCBinary(state unsafe.Pointer) (string, error)
	// ExtractSignalsBinary extracts the signals of a binary CAN frame.
	ExtractSignalsBinary(state unsafe.Pointer, id CANID, dlc DLC, data []byte) (string, error)

	// Group 3: raw bytes both ways.

	// BuildFrameBin builds a CAN frame from signal values and returns its payload.
	BuildFrameBin(state unsafe.Pointer, id CANID, dlc DLC, signals []SignalInjection) ([]byte, error)
	// UpdateFrameBin rewrites signals in an existing payload and returns the new payload.
	UpdateFrameBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte, signals []SignalInjection) ([]byte, error)
	// ExtractSignalsBin extracts signals as the packed binary the caller parses.
	ExtractSignalsBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte) ([]byte, error)
}
