//go:build !cgo || !linux

package aletheia

import "unsafe"

// FFIBackend requires cgo. This stub exists so the package compiles with
// CGO_ENABLED=0 (e.g. for MockBackend-only testing on non-Linux platforms).
type FFIBackend struct{}

// NewFFIBackend returns an error because cgo/linux is not available in this build.
func NewFFIBackend(_ string, _ ...FFIBackendOption) (*FFIBackend, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// Init is unavailable without cgo.
func (b *FFIBackend) Init() (unsafe.Pointer, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// Process is unavailable without cgo.
func (b *FFIBackend) Process(_ unsafe.Pointer, _ string) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// SendFrameBinary is unavailable without cgo.
func (b *FFIBackend) SendFrameBinary(_ unsafe.Pointer, _ Timestamp, _ CanID, _ DLC, _ []byte) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// SendErrorBinary is unavailable without cgo.
func (b *FFIBackend) SendErrorBinary(_ unsafe.Pointer, _ Timestamp) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// SendRemoteBinary is unavailable without cgo.
func (b *FFIBackend) SendRemoteBinary(_ unsafe.Pointer, _ Timestamp, _ CanID) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// StartStreamBinary is unavailable without cgo.
func (b *FFIBackend) StartStreamBinary(_ unsafe.Pointer) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// EndStreamBinary is unavailable without cgo.
func (b *FFIBackend) EndStreamBinary(_ unsafe.Pointer) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// FormatDbcBinary is unavailable without cgo.
func (b *FFIBackend) FormatDbcBinary(_ unsafe.Pointer) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// ExtractSignalsBinary is unavailable without cgo.
func (b *FFIBackend) ExtractSignalsBinary(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// BuildFrameBinary is unavailable without cgo.
func (b *FFIBackend) BuildFrameBinary(_ unsafe.Pointer, _ CanID, _ DLC, _ uint32, _ []uint32, _ []int64, _ []int64) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// UpdateFrameBinary is unavailable without cgo.
func (b *FFIBackend) UpdateFrameBinary(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte, _ uint32, _ []uint32, _ []int64, _ []int64) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// BuildFrameBin is unavailable without cgo.
func (b *FFIBackend) BuildFrameBin(_ unsafe.Pointer, _ CanID, _ DLC, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// UpdateFrameBin is unavailable without cgo.
func (b *FFIBackend) UpdateFrameBin(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// ExtractSignalsBin is unavailable without cgo.
func (b *FFIBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CanID, _ DLC, _ []byte) ([]byte, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// Close is a no-op without cgo.
func (b *FFIBackend) Close(_ unsafe.Pointer) {}
