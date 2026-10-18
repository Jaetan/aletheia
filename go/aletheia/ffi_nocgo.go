//go:build !cgo || !linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

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
func (*FFIBackend) Init() (State, error) { return 0, errNoCgo() }

// Process refuses.
func (*FFIBackend) Process(_ State, _ string) (string, error) { return "", errNoCgo() }

// SendFrameBinary refuses.
func (*FFIBackend) SendFrameBinary(_ State, _ Timestamp, _ CANID, _ DLC, _ []byte, _ *bool, _ *bool) (string, error) {
	return "", errNoCgo()
}

// SendErrorBinary refuses.
func (*FFIBackend) SendErrorBinary(_ State, _ Timestamp) (string, error) {
	return "", errNoCgo()
}

// SendRemoteBinary refuses.
func (*FFIBackend) SendRemoteBinary(_ State, _ Timestamp, _ CANID) (string, error) {
	return "", errNoCgo()
}

// StartStreamBinary refuses.
func (*FFIBackend) StartStreamBinary(_ State) (string, error) { return "", errNoCgo() }

// EndStreamBinary refuses.
func (*FFIBackend) EndStreamBinary(_ State) (string, error) { return "", errNoCgo() }

// FormatDBCBinary refuses.
func (*FFIBackend) FormatDBCBinary(_ State) (string, error) { return "", errNoCgo() }

// ExtractSignalsBinary refuses.
func (*FFIBackend) ExtractSignalsBinary(_ State, _ CANID, _ DLC, _ []byte) (string, error) {
	return "", errNoCgo()
}

// BuildFrameBin refuses.
func (*FFIBackend) BuildFrameBin(_ State, _ CANID, _ DLC, _ []SignalInjection) ([]byte, error) {
	return nil, errNoCgo()
}

// UpdateFrameBin refuses.
func (*FFIBackend) UpdateFrameBin(_ State, _ CANID, _ DLC, _ []byte, _ []SignalInjection) ([]byte, error) {
	return nil, errNoCgo()
}

// ExtractSignalsBin refuses.
func (*FFIBackend) ExtractSignalsBin(_ State, _ CANID, _ DLC, _ []byte) ([]byte, error) {
	return nil, errNoCgo()
}

// Close has nothing to close.
func (*FFIBackend) Close(_ State) {}

// formatRationalFFI refuses: the rational printer every binding shares is the
// kernel's, and FromDecimal in decimal_nocgo.go refuses for the same reason.
func formatRationalFFI(_ int64, _ int64) (string, error) {
	return "", ffiError("formatRational requires cgo on linux; build with CGO_ENABLED=1")
}

// The interface is satisfied here as it is in the cgo file, so a drift in its
// signatures fails this build rather than the first caller's.
var _ Backend = (*FFIBackend)(nil)
