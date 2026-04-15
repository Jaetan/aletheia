//go:build cgo && linux

package aletheia

// FFI backend — loads libaletheia-ffi.so via cgo + dlopen.
//
// This file uses cgo to call dlopen/dlsym from <dlfcn.h>. The GHC RTS
// is initialized exactly once per process (via sync.Once) and never
// finalized — hs_exit() is not supported for reinitialization.

// #cgo LDFLAGS: -ldl
//
// #include <dlfcn.h>
// #include <stdint.h>
// #include <stdio.h>
// #include <stdlib.h>
// #include <string.h>
//
// // Typed trampolines so cgo can call function pointers loaded via dlsym.
// // cgo cannot call through C function pointer variables directly.
//
// static void call_hs_init(void *fn, int *argc, char ***argv) {
//     ((void (*)(int*, char***))fn)(argc, argv);
// }
// static void* call_init(void *fn) {
//     return ((void* (*)(void))fn)();
// }
// static char* call_process(void *fn, void *state, const char *input) {
//     return ((char* (*)(void*, const char*))fn)(state, input);
// }
// static void call_free_str(void *fn, char *ptr) {
//     ((void (*)(char*))fn)(ptr);
// }
// static void call_close(void *fn, void *state) {
//     ((void (*)(void*))fn)(state);
// }
// static char* call_send_frame(void *fn, void *state, uint64_t ts,
//     uint32_t id, uint8_t ext, uint8_t dlc, uint8_t *data, uint8_t len) {
//     return ((char* (*)(void*, uint64_t, uint32_t, uint8_t, uint8_t,
//                         uint8_t*, uint8_t))fn)(state, ts, id, ext, dlc, data, len);
// }
// static char* call_send_error(void *fn, void *state, uint64_t ts) {
//     return ((char* (*)(void*, uint64_t))fn)(state, ts);
// }
// static char* call_send_remote(void *fn, void *state, uint64_t ts,
//     uint32_t id, uint8_t ext) {
//     return ((char* (*)(void*, uint64_t, uint32_t, uint8_t))fn)(state, ts, id, ext);
// }
// static char* call_start_stream(void *fn, void *state) {
//     return ((char* (*)(void*))fn)(state);
// }
// static char* call_end_stream(void *fn, void *state) {
//     return ((char* (*)(void*))fn)(state);
// }
// static char* call_format_dbc(void *fn, void *state) {
//     return ((char* (*)(void*))fn)(state);
// }
// static char* call_extract_signals(void *fn, void *state,
//     uint32_t id, uint8_t ext, uint8_t dlc, uint8_t *data, uint8_t len) {
//     return ((char* (*)(void*, uint32_t, uint8_t, uint8_t,
//                         uint8_t*, uint8_t))fn)(state, id, ext, dlc, data, len);
// }
// static char* call_build_frame(void *fn, void *state,
//     uint32_t id, uint8_t ext, uint8_t dlc,
//     uint32_t numSignals, uint32_t *indices, int64_t *nums, int64_t *dens) {
//     return ((char* (*)(void*, uint32_t, uint8_t, uint8_t,
//                         uint32_t, uint32_t*, int64_t*, int64_t*))fn)(
//         state, id, ext, dlc, numSignals, indices, nums, dens);
// }
// static char* call_update_frame(void *fn, void *state,
//     uint32_t id, uint8_t ext, uint8_t dlc,
//     uint8_t *data, uint8_t dataLen,
//     uint32_t numSignals, uint32_t *indices, int64_t *nums, int64_t *dens) {
//     return ((char* (*)(void*, uint32_t, uint8_t, uint8_t,
//                         uint8_t*, uint8_t,
//                         uint32_t, uint32_t*, int64_t*, int64_t*))fn)(
//         state, id, ext, dlc, data, dataLen, numSignals, indices, nums, dens);
// }
// static int8_t call_build_frame_bin(void *fn, void *state,
//     uint32_t id, uint8_t ext, uint8_t dlc,
//     uint32_t numSignals, uint32_t *indices, int64_t *nums, int64_t *dens,
//     uint8_t *outBuf, char **outErr) {
//     return ((int8_t (*)(void*, uint32_t, uint8_t, uint8_t,
//                          uint32_t, uint32_t*, int64_t*, int64_t*,
//                          uint8_t*, char**))fn)(
//         state, id, ext, dlc, numSignals, indices, nums, dens, outBuf, outErr);
// }
// static int8_t call_update_frame_bin(void *fn, void *state,
//     uint32_t id, uint8_t ext, uint8_t dlc,
//     uint8_t *data, uint8_t dataLen,
//     uint32_t numSignals, uint32_t *indices, int64_t *nums, int64_t *dens,
//     uint8_t *outBuf, char **outErr) {
//     return ((int8_t (*)(void*, uint32_t, uint8_t, uint8_t,
//                          uint8_t*, uint8_t,
//                          uint32_t, uint32_t*, int64_t*, int64_t*,
//                          uint8_t*, char**))fn)(
//         state, id, ext, dlc, data, dataLen, numSignals, indices, nums, dens, outBuf, outErr);
// }
//
// static int8_t call_extract_signals_bin(void *fn, void *state,
//     uint32_t id, uint8_t ext, uint8_t dlc,
//     uint8_t *data, uint8_t dataLen,
//     uint8_t **outBuf, uint32_t *outSize, char **outErr) {
//     return ((int8_t (*)(void*, uint32_t, uint8_t, uint8_t,
//                          uint8_t*, uint8_t,
//                          uint8_t**, uint32_t*, char**))fn)(
//         state, id, ext, dlc, data, dataLen, outBuf, outSize, outErr);
// }
// static void call_free_buf(void *fn, uint8_t *ptr) {
//     ((void (*)(uint8_t*))fn)(ptr);
// }
//
// // call_hs_init_rts builds argv and calls hs_init with +RTS -N<cores> -RTS.
// // Keeps argv in C heap — hs_init may retain pointers.
// static void call_hs_init_rts(void *fn, int cores) {
//     char buf[16];
//     snprintf(buf, sizeof(buf), "-N%d", cores);
//     char *args[4];
//     args[0] = strdup("aletheia");
//     args[1] = strdup("+RTS");
//     args[2] = strdup(buf);
//     args[3] = strdup("-RTS");
//     int argc = 4;
//     char **argv = args;
//     ((void (*)(int*, char***))fn)(&argc, &argv);
//     // Intentionally not freed — GHC RTS may retain argv pointers.
// }
import "C"

import (
	"context"
	"fmt"
	"log/slog"
	"math"
	"path/filepath"
	"runtime"
	"sync"
	"unsafe"
)

var (
	hsInitMu    sync.Mutex
	hsInitDone  bool
	hsInitCores int
)

// FFIBackend implements [Backend] by loading libaletheia-ffi.so via dlopen.
//
// Requirements:
//   - Linux (uses <dlfcn.h> for dlopen/dlsym)
//   - CGO_ENABLED=1 (links -ldl for dynamic loading)
//   - libaletheia-ffi.so built from the Agda core
//
// The GHC runtime system is initialized once per process via hs_init and
// never finalized. All FFI calls are pinned to OS threads via
// [runtime.LockOSThread] because the GHC RTS has per-capability state.
type FFIBackend struct {
	handle              unsafe.Pointer // dlopen handle
	initFn              unsafe.Pointer
	processFn           unsafe.Pointer
	sendFrameFn         unsafe.Pointer
	sendErrorFn         unsafe.Pointer
	sendRemoteFn        unsafe.Pointer
	startStreamFn       unsafe.Pointer
	endStreamFn         unsafe.Pointer
	formatDbcFn         unsafe.Pointer
	extractSignalsFn    unsafe.Pointer
	buildFrameFn        unsafe.Pointer
	updateFrameFn       unsafe.Pointer
	buildFrameBinFn     unsafe.Pointer
	updateFrameBinFn    unsafe.Pointer
	extractSignalsBinFn unsafe.Pointer
	freeBufFn           unsafe.Pointer
	freeStrFn           unsafe.Pointer
	closeFn             unsafe.Pointer
}

func (*FFIBackend) backend() {}

func loadSym(handle unsafe.Pointer, name string) (unsafe.Pointer, error) {
	cName := C.CString(name)
	defer C.free(unsafe.Pointer(cName))

	C.dlerror() // clear previous errors
	sym := C.dlsym(handle, cName)
	errStr := C.dlerror()
	if errStr != nil {
		return nil, ffiError("dlsym failed for " + name + ": " + C.GoString(errStr))
	}
	return sym, nil
}

// NewFFIBackend opens libaletheia-ffi.so at the given path and initializes
// the GHC RTS. The library handle is never closed — the GHC RTS owns threads
// that reference it.
func NewFFIBackend(libPath string, opts ...FFIBackendOption) (*FFIBackend, error) {
	// Pin goroutine to OS thread — dlerror() is thread-local, and goroutine
	// migration between dlsym and dlerror in loadSym could return stale data.
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	libPath = filepath.Clean(libPath)
	cPath := C.CString(libPath)
	defer C.free(unsafe.Pointer(cPath))

	handle := C.dlopen(cPath, C.RTLD_NOW|C.RTLD_LOCAL)
	if handle == nil {
		return nil, ffiError("dlopen failed: " + C.GoString(C.dlerror()))
	}
	// Close handle on error; the library is intentionally kept open on success
	// because the GHC RTS owns threads that reference it.
	closeOnErr := true
	defer func() {
		if closeOnErr {
			C.dlclose(handle)
		}
	}()

	// Required symbols from libaletheia-ffi.so (keep in sync with the
	// loadSym calls below — a drifted comment is a finding):
	//   hs_init                       — GHC RTS initialization (called once per process)
	//   aletheia_init                 — create a new session (returns StablePtr)
	//   aletheia_process              — send JSON command, receive JSON response
	//   aletheia_send_frame           — binary CAN frame (streaming LTL hot path)
	//   aletheia_send_error           — CAN error frame event
	//   aletheia_send_remote          — CAN remote frame event
	//   aletheia_start_stream         — begin streaming (no JSON input)
	//   aletheia_end_stream           — finalize streaming (no JSON input)
	//   aletheia_format_dbc           — export loaded DBC (no JSON input)
	//   aletheia_extract_signals      — signal extraction, JSON response
	//   aletheia_build_frame          — frame building from signal indices, JSON response
	//   aletheia_update_frame         — frame update from signal indices, JSON response
	//   aletheia_build_frame_bin      — frame building, binary response (hot path)
	//   aletheia_update_frame_bin     — frame update, binary response (hot path)
	//   aletheia_extract_signals_bin  — signal extraction, binary response (hot path)
	//   aletheia_free_buf             — free Haskell-allocated binary buffers
	//   aletheia_free_str             — free Haskell-allocated response strings
	//   aletheia_close                — finalize and free session state
	hsInit, err := loadSym(handle, "hs_init")
	if err != nil {
		return nil, err
	}
	initFn, err := loadSym(handle, "aletheia_init")
	if err != nil {
		return nil, err
	}
	processFn, err := loadSym(handle, "aletheia_process")
	if err != nil {
		return nil, err
	}
	sendFrameFn, err := loadSym(handle, "aletheia_send_frame")
	if err != nil {
		return nil, err
	}
	sendErrorFn, err := loadSym(handle, "aletheia_send_error")
	if err != nil {
		return nil, err
	}
	sendRemoteFn, err := loadSym(handle, "aletheia_send_remote")
	if err != nil {
		return nil, err
	}
	startStreamFn, err := loadSym(handle, "aletheia_start_stream")
	if err != nil {
		return nil, err
	}
	endStreamFn, err := loadSym(handle, "aletheia_end_stream")
	if err != nil {
		return nil, err
	}
	formatDbcFn, err := loadSym(handle, "aletheia_format_dbc")
	if err != nil {
		return nil, err
	}
	extractSignalsFn, err := loadSym(handle, "aletheia_extract_signals")
	if err != nil {
		return nil, err
	}
	buildFrameFn, err := loadSym(handle, "aletheia_build_frame")
	if err != nil {
		return nil, err
	}
	updateFrameFn, err := loadSym(handle, "aletheia_update_frame")
	if err != nil {
		return nil, err
	}
	buildFrameBinFn, err := loadSym(handle, "aletheia_build_frame_bin")
	if err != nil {
		return nil, err
	}
	updateFrameBinFn, err := loadSym(handle, "aletheia_update_frame_bin")
	if err != nil {
		return nil, err
	}
	extractSignalsBinFn, err := loadSym(handle, "aletheia_extract_signals_bin")
	if err != nil {
		return nil, err
	}
	freeBufFn, err := loadSym(handle, "aletheia_free_buf")
	if err != nil {
		return nil, err
	}
	freeStrFn, err := loadSym(handle, "aletheia_free_str")
	if err != nil {
		return nil, err
	}
	closeFn, err := loadSym(handle, "aletheia_close")
	if err != nil {
		return nil, err
	}

	// Apply options.
	cfg := ffiConfig{rtsCores: 1}
	for _, o := range opts {
		o(&cfg)
	}

	// Initialize GHC RTS exactly once per process.
	if cfg.rtsCores < 1 {
		return nil, validationError(fmt.Sprintf("rtsCores must be >= 1, got %d", cfg.rtsCores))
	}
	if cfg.rtsCores > math.MaxInt32 {
		return nil, validationError(fmt.Sprintf("rtsCores %d exceeds C int range (max %d)", cfg.rtsCores, math.MaxInt32))
	}
	hsInitMu.Lock()
	defer hsInitMu.Unlock()
	if !hsInitDone {
		if cfg.rtsCores > 1 {
			C.call_hs_init_rts(hsInit, C.int(cfg.rtsCores))
		} else {
			C.call_hs_init(hsInit, nil, nil)
		}
		hsInitCores = cfg.rtsCores
		hsInitDone = true
	} else if cfg.rtsCores != hsInitCores && cfg.logger != nil {
		cfg.logger.LogAttrs(context.Background(), slog.LevelWarn, "rts.cores_mismatch",
			slog.Int("active_cores", hsInitCores),
			slog.Int("requested_cores", cfg.rtsCores))
	}

	closeOnErr = false
	return &FFIBackend{
		handle:              handle,
		initFn:              initFn,
		processFn:           processFn,
		sendFrameFn:         sendFrameFn,
		sendErrorFn:         sendErrorFn,
		sendRemoteFn:        sendRemoteFn,
		startStreamFn:       startStreamFn,
		endStreamFn:         endStreamFn,
		formatDbcFn:         formatDbcFn,
		extractSignalsFn:    extractSignalsFn,
		buildFrameFn:        buildFrameFn,
		updateFrameFn:       updateFrameFn,
		buildFrameBinFn:     buildFrameBinFn,
		updateFrameBinFn:    updateFrameBinFn,
		extractSignalsBinFn: extractSignalsBinFn,
		freeBufFn:           freeBufFn,
		freeStrFn:           freeStrFn,
		closeFn:             closeFn,
	}, nil
}

// Init creates a new Aletheia session. The returned pointer is an opaque
// StablePtr managed by the Haskell runtime.
func (b *FFIBackend) Init() (unsafe.Pointer, error) {
	// Pin goroutine to OS thread — GHC RTS has per-capability state.
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	state := C.call_init(b.initFn)
	if state == nil {
		return nil, ffiError("aletheia_init returned null")
	}
	return state, nil
}

// Process sends a JSON command and returns the JSON response.
func (b *FFIBackend) Process(state unsafe.Pointer, input string) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	cInput := C.CString(input)
	defer C.free(unsafe.Pointer(cInput))

	result := C.call_process(b.processFn, state, cInput)
	if result == nil {
		return "", ffiError("aletheia_process returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// SendFrameBinary sends a CAN frame via the binary FFI entry point,
// bypassing JSON serialization on the input side.
func (b *FFIBackend) SendFrameBinary(state unsafe.Pointer, ts Timestamp, id CanID, dlc DLC, data []byte) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	if ts.Microseconds < 0 {
		return "", validationError("timestamp must be non-negative")
	}

	if len(data) > 64 {
		return "", validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (64)", len(data)))
	}

	var dataPtr *C.uint8_t
	if len(data) > 0 {
		dataPtr = (*C.uint8_t)(unsafe.Pointer(&data[0]))
	}

	// C.uint8_t(len(data)) is safe: the bounds check above guarantees
	// len(data) <= 64 < 256, so the cast never truncates.
	result := C.call_send_frame(
		b.sendFrameFn, state,
		C.uint64_t(ts.Microseconds),
		C.uint32_t(id.Value()),
		ext,
		C.uint8_t(dlc.Value()),
		dataPtr,
		C.uint8_t(len(data)),
	)
	if result == nil {
		return "", ffiError("aletheia_send_frame returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// SendErrorBinary sends a CAN error event via the binary FFI entry point.
func (b *FFIBackend) SendErrorBinary(state unsafe.Pointer, ts Timestamp) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	if ts.Microseconds < 0 {
		return "", validationError("timestamp must be non-negative")
	}

	result := C.call_send_error(b.sendErrorFn, state, C.uint64_t(ts.Microseconds))
	if result == nil {
		return "", ffiError("aletheia_send_error returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// SendRemoteBinary sends a CAN remote frame event via the binary FFI entry point.
func (b *FFIBackend) SendRemoteBinary(state unsafe.Pointer, ts Timestamp, id CanID) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	if ts.Microseconds < 0 {
		return "", validationError("timestamp must be non-negative")
	}

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	result := C.call_send_remote(b.sendRemoteFn, state, C.uint64_t(ts.Microseconds), C.uint32_t(id.Value()), ext)
	if result == nil {
		return "", ffiError("aletheia_send_remote returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// StartStreamBinary begins streaming mode via the binary FFI entry point.
func (b *FFIBackend) StartStreamBinary(state unsafe.Pointer) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	result := C.call_start_stream(b.startStreamFn, state)
	if result == nil {
		return "", ffiError("aletheia_start_stream returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// EndStreamBinary finalizes streaming and returns verdicts via the binary FFI entry point.
func (b *FFIBackend) EndStreamBinary(state unsafe.Pointer) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	result := C.call_end_stream(b.endStreamFn, state)
	if result == nil {
		return "", ffiError("aletheia_end_stream returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// FormatDbcBinary returns the loaded DBC as JSON via the binary FFI entry point.
func (b *FFIBackend) FormatDbcBinary(state unsafe.Pointer) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	result := C.call_format_dbc(b.formatDbcFn, state)
	if result == nil {
		return "", ffiError("aletheia_format_dbc returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// ExtractSignalsBinary extracts signals from a binary CAN frame via the binary FFI entry point.
func (b *FFIBackend) ExtractSignalsBinary(state unsafe.Pointer, id CanID, dlc DLC, data []byte) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	if len(data) > 64 {
		return "", validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (64)", len(data)))
	}

	var dataPtr *C.uint8_t
	if len(data) > 0 {
		dataPtr = (*C.uint8_t)(unsafe.Pointer(&data[0]))
	}

	result := C.call_extract_signals(
		b.extractSignalsFn, state,
		C.uint32_t(id.Value()),
		ext,
		C.uint8_t(dlc.Value()),
		dataPtr,
		C.uint8_t(len(data)),
	)
	if result == nil {
		return "", ffiError("aletheia_extract_signals returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// BuildFrameBinary builds a CAN frame from signal index-value pairs via the binary FFI entry point.
func (b *FFIBackend) BuildFrameBinary(state unsafe.Pointer, id CanID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	var indicesPtr *C.uint32_t
	var numsPtr *C.int64_t
	var densPtr *C.int64_t
	if numSignals > 0 {
		indicesPtr = (*C.uint32_t)(unsafe.Pointer(&indices[0]))
		numsPtr = (*C.int64_t)(unsafe.Pointer(&nums[0]))
		densPtr = (*C.int64_t)(unsafe.Pointer(&dens[0]))
	}

	result := C.call_build_frame(
		b.buildFrameFn, state,
		C.uint32_t(id.Value()),
		ext,
		C.uint8_t(dlc.Value()),
		C.uint32_t(numSignals),
		indicesPtr,
		numsPtr,
		densPtr,
	)
	if result == nil {
		return "", ffiError("aletheia_build_frame returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// UpdateFrameBinary updates signals in a CAN frame by index via the binary FFI entry point.
func (b *FFIBackend) UpdateFrameBinary(state unsafe.Pointer, id CanID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	if len(data) > 64 {
		return "", validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (64)", len(data)))
	}

	var dataPtr *C.uint8_t
	if len(data) > 0 {
		dataPtr = (*C.uint8_t)(unsafe.Pointer(&data[0]))
	}

	var indicesPtr *C.uint32_t
	var numsPtr *C.int64_t
	var densPtr *C.int64_t
	if numSignals > 0 {
		indicesPtr = (*C.uint32_t)(unsafe.Pointer(&indices[0]))
		numsPtr = (*C.int64_t)(unsafe.Pointer(&nums[0]))
		densPtr = (*C.int64_t)(unsafe.Pointer(&dens[0]))
	}

	result := C.call_update_frame(
		b.updateFrameFn, state,
		C.uint32_t(id.Value()),
		ext,
		C.uint8_t(dlc.Value()),
		dataPtr,
		C.uint8_t(len(data)),
		C.uint32_t(numSignals),
		indicesPtr,
		numsPtr,
		densPtr,
	)
	if result == nil {
		return "", ffiError("aletheia_update_frame returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// BuildFrameBin builds a CAN frame returning raw payload bytes, bypassing JSON entirely.
func (b *FFIBackend) BuildFrameBin(state unsafe.Pointer, id CanID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	var indicesPtr *C.uint32_t
	var numsPtr *C.int64_t
	var densPtr *C.int64_t
	if numSignals > 0 {
		indicesPtr = (*C.uint32_t)(unsafe.Pointer(&indices[0]))
		numsPtr = (*C.int64_t)(unsafe.Pointer(&nums[0]))
		densPtr = (*C.int64_t)(unsafe.Pointer(&dens[0]))
	}

	expectedBytes := dlc.ToBytes()
	outBuf := make([]byte, expectedBytes)
	var outBufPtr *C.uint8_t
	if expectedBytes > 0 {
		outBufPtr = (*C.uint8_t)(unsafe.Pointer(&outBuf[0]))
	}
	var outErr *C.char

	status := C.call_build_frame_bin(
		b.buildFrameBinFn, state,
		C.uint32_t(id.Value()),
		ext,
		C.uint8_t(dlc.Value()),
		C.uint32_t(numSignals),
		indicesPtr,
		numsPtr,
		densPtr,
		outBufPtr,
		&outErr,
	)
	if status != 0 {
		var msg string
		if outErr != nil {
			msg = C.GoString(outErr)
			C.call_free_str(b.freeStrFn, outErr)
		} else {
			msg = fmt.Sprintf("build_frame_bin returned status %d with null error message", status)
		}
		return nil, protocolError(msg)
	}
	return outBuf, nil
}

// UpdateFrameBin updates a CAN frame returning raw payload bytes, bypassing JSON entirely.
func (b *FFIBackend) UpdateFrameBin(state unsafe.Pointer, id CanID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	// Cap at the CAN-FD maximum payload size; every other data-accepting
	// method (SendFrameBinary, ExtractSignalsBinary, UpdateFrameBinary)
	// applies the same bound before taking &data[0] into cgo.
	if len(data) > 64 {
		return nil, validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (64)", len(data)))
	}

	var dataPtr *C.uint8_t
	if len(data) > 0 {
		dataPtr = (*C.uint8_t)(unsafe.Pointer(&data[0]))
	}

	var indicesPtr *C.uint32_t
	var numsPtr *C.int64_t
	var densPtr *C.int64_t
	if numSignals > 0 {
		indicesPtr = (*C.uint32_t)(unsafe.Pointer(&indices[0]))
		numsPtr = (*C.int64_t)(unsafe.Pointer(&nums[0]))
		densPtr = (*C.int64_t)(unsafe.Pointer(&dens[0]))
	}

	expectedBytes := dlc.ToBytes()
	outBuf := make([]byte, expectedBytes)
	var outBufPtr *C.uint8_t
	if expectedBytes > 0 {
		outBufPtr = (*C.uint8_t)(unsafe.Pointer(&outBuf[0]))
	}
	var outErr *C.char

	status := C.call_update_frame_bin(
		b.updateFrameBinFn, state,
		C.uint32_t(id.Value()),
		ext,
		C.uint8_t(dlc.Value()),
		dataPtr,
		C.uint8_t(len(data)),
		C.uint32_t(numSignals),
		indicesPtr,
		numsPtr,
		densPtr,
		outBufPtr,
		&outErr,
	)
	if status != 0 {
		var msg string
		if outErr != nil {
			msg = C.GoString(outErr)
			C.call_free_str(b.freeStrFn, outErr)
		} else {
			msg = fmt.Sprintf("update_frame_bin returned status %d with null error message", status)
		}
		return nil, protocolError(msg)
	}
	return outBuf, nil
}

// ExtractSignalsBin extracts signals returning packed binary, bypassing JSON entirely.
func (b *FFIBackend) ExtractSignalsBin(state unsafe.Pointer, id CanID, dlc DLC, data []byte) ([]byte, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	// Cap at the CAN-FD maximum payload size; every other data-accepting
	// method applies the same bound before taking &data[0] into cgo.
	if len(data) > 64 {
		return nil, validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (64)", len(data)))
	}

	var dataPtr *C.uint8_t
	if len(data) > 0 {
		dataPtr = (*C.uint8_t)(unsafe.Pointer(&data[0]))
	}

	var outBuf *C.uint8_t
	var outSize C.uint32_t
	var outErr *C.char

	status := C.call_extract_signals_bin(
		b.extractSignalsBinFn, state,
		C.uint32_t(id.Value()),
		ext,
		C.uint8_t(dlc.Value()),
		dataPtr,
		C.uint8_t(len(data)),
		&outBuf,
		&outSize,
		&outErr,
	)
	if status != 0 {
		var msg string
		if outErr != nil {
			msg = C.GoString(outErr)
			C.call_free_str(b.freeStrFn, outErr)
		} else {
			msg = fmt.Sprintf("extract_signals_bin returned status %d with null error message", status)
		}
		return nil, protocolError(msg)
	}
	// Guard against theoretical overflow when casting outSize (uint32) to C.int (int32).
	if outSize > math.MaxInt32 {
		C.call_free_buf(b.freeBufFn, outBuf)
		return nil, protocolError(fmt.Sprintf("extract_signals_bin returned outSize %d exceeding C.int range", outSize))
	}
	result := C.GoBytes(unsafe.Pointer(outBuf), C.int(outSize))
	C.call_free_buf(b.freeBufFn, outBuf)
	return result, nil
}

// Close finalizes and frees the session state.
func (b *FFIBackend) Close(state unsafe.Pointer) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	C.call_close(b.closeFn, state)
}
