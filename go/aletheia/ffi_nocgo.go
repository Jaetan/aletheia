//go:build !cgo || !linux

package aletheia

import "unsafe"

// FFIBackend requires cgo. This stub exists so the package compiles with
// CGO_ENABLED=0 (e.g. for MockBackend-only testing on non-Linux platforms).
type FFIBackend struct{}

// NewFFIBackend returns an error because cgo/linux is not available in this build.
func NewFFIBackend(_ string, _ ...FFIBackendOption) (*FFIBackend, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1 on linux")
}

// Init is unavailable without cgo.
func (b *FFIBackend) Init() (unsafe.Pointer, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1 on linux")
}

// Process is unavailable without cgo.
func (b *FFIBackend) Process(_ unsafe.Pointer, _ string) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1 on linux")
}

// SendFrameBinary is unavailable without cgo.
func (b *FFIBackend) SendFrameBinary(_ unsafe.Pointer, _ Timestamp, _ CanID, _ DLC, _ []byte) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1 on linux")
}

// Close is a no-op without cgo.
func (b *FFIBackend) Close(_ unsafe.Pointer) {}
