//go:build !cgo || !linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import "unsafe"

// The FFIBackend of a build without cgo, or off Linux. It carries the whole
// surface its cgo twin does, so the package and the code calling it compile
// either way and MockBackend stays usable, and every endpoint refuses, since
// reaching the kernel needs dlopen. The build tag is the negation of the one
// on ffi.go, so exactly one of the two is compiled.
type FFIBackend struct{}

func (*FFIBackend) backend() {}

// errNoCgo is the refusal the whole surface answers with.
func errNoCgo() error {
	return ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// NewFFIBackend refuses: there is no way to open the library.
func NewFFIBackend(_ string, _ ...FFIBackendOption) (*FFIBackend, error) {
	return nil, errNoCgo()
}

// NewFFIBackendFromEnv refuses for the same reason, whatever ALETHEIA_LIB names.
func NewFFIBackendFromEnv(_ ...FFIBackendOption) (*FFIBackend, error) {
	return nil, errNoCgo()
}

// StablePtrCount is zero: no session can be opened without cgo.
func StablePtrCount() int64 { return 0 }

// Every endpoint below refuses. The signatures are the interface's, which the
// assertion at the end of the file holds them to.

// Init refuses.
func (*FFIBackend) Init() (unsafe.Pointer, error) { return nil, errNoCgo() }

// Process refuses.
func (*FFIBackend) Process(_ unsafe.Pointer, _ string) (string, error) { return "", errNoCgo() }

// SendFrameBinary refuses.
func (*FFIBackend) SendFrameBinary(_ unsafe.Pointer, _ Timestamp, _ CANID, _ DLC, _ []byte, _ *bool, _ *bool) (string, error) {
	return "", errNoCgo()
}

// SendErrorBinary refuses.
func (*FFIBackend) SendErrorBinary(_ unsafe.Pointer, _ Timestamp) (string, error) {
	return "", errNoCgo()
}

// SendRemoteBinary refuses.
func (*FFIBackend) SendRemoteBinary(_ unsafe.Pointer, _ Timestamp, _ CANID) (string, error) {
	return "", errNoCgo()
}

// StartStreamBinary refuses.
func (*FFIBackend) StartStreamBinary(_ unsafe.Pointer) (string, error) { return "", errNoCgo() }

// EndStreamBinary refuses.
func (*FFIBackend) EndStreamBinary(_ unsafe.Pointer) (string, error) { return "", errNoCgo() }

// FormatDBCBinary refuses.
func (*FFIBackend) FormatDBCBinary(_ unsafe.Pointer) (string, error) { return "", errNoCgo() }

// ExtractSignalsBinary refuses.
func (*FFIBackend) ExtractSignalsBinary(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte) (string, error) {
	return "", errNoCgo()
}

// BuildFrameBin refuses.
func (*FFIBackend) BuildFrameBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []SignalInjection) ([]byte, error) {
	return nil, errNoCgo()
}

// UpdateFrameBin refuses.
func (*FFIBackend) UpdateFrameBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte, _ []SignalInjection) ([]byte, error) {
	return nil, errNoCgo()
}

// ExtractSignalsBin refuses.
func (*FFIBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte) ([]byte, error) {
	return nil, errNoCgo()
}

// Close has nothing to close.
func (*FFIBackend) Close(_ unsafe.Pointer) {}

// formatRationalFFI refuses: the rational printer every binding shares is the
// kernel's, and FromDecimal in decimal_nocgo.go refuses for the same reason.
func formatRationalFFI(_ int64, _ int64) (string, error) {
	return "", ffiError("formatRational requires cgo on linux; build with CGO_ENABLED=1")
}

// The interface is satisfied here as it is in the cgo file, so a drift in its
// signatures fails this build rather than the first caller's.
var _ Backend = (*FFIBackend)(nil)
