//go:build !cgo || !linux

package aletheia

import "unsafe"

// FFIBackend requires cgo. This stub exists so the package compiles with
// CGO_ENABLED=0 (e.g. for MockBackend-only testing on non-Linux platforms).
type FFIBackend struct{}

func (*FFIBackend) backend() {}

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
func (b *FFIBackend) SendFrameBinary(_ unsafe.Pointer, _ Timestamp, _ CANID, _ DLC, _ []byte, _ *bool, _ *bool) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// Compile-time assertion that *FFIBackend satisfies the Backend interface
// under the !cgo || !linux build tag, mirroring the cgo branch in ffi.go.
// This catches Backend-interface signature drift at `go build` time rather
// than at the first downstream caller — the gap that let R19P2 cluster 18
// phase A (brs/esi *bool args) miss this stub for the !cgo build.
var _ Backend = (*FFIBackend)(nil)

// SendErrorBinary is unavailable without cgo.
func (b *FFIBackend) SendErrorBinary(_ unsafe.Pointer, _ Timestamp) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// SendRemoteBinary is unavailable without cgo.
func (b *FFIBackend) SendRemoteBinary(_ unsafe.Pointer, _ Timestamp, _ CANID) (string, error) {
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

// FormatDBCBinary is unavailable without cgo.
func (b *FFIBackend) FormatDBCBinary(_ unsafe.Pointer) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// ExtractSignalsBinary is unavailable without cgo.
func (b *FFIBackend) ExtractSignalsBinary(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte) (string, error) {
	return "", ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// BuildFrameBin is unavailable without cgo.
func (b *FFIBackend) BuildFrameBin(_ unsafe.Pointer, _ CANID, _ DLC, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// UpdateFrameBin is unavailable without cgo.
func (b *FFIBackend) UpdateFrameBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte, _ uint32, _ []uint32, _ []int64, _ []int64) ([]byte, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// ExtractSignalsBin is unavailable without cgo.
func (b *FFIBackend) ExtractSignalsBin(_ unsafe.Pointer, _ CANID, _ DLC, _ []byte) ([]byte, error) {
	return nil, ffiError("ffi backend requires cgo on linux; build with CGO_ENABLED=1")
}

// Close is a no-op without cgo.
func (b *FFIBackend) Close(_ unsafe.Pointer) {}

// tryFormatRationalFFI is a no-FFI stub.  Always returns ("", false)
// so `formatRational` falls back to the local Go algorithm.  In !cgo
// builds the renderer cannot reach the Agda kernel — there is no .so
// to dlopen — so we rely on the local algorithm for output parity.
func tryFormatRationalFFI(_ int64, _ int64) (string, bool) {
	return "", false
}
