//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// FFI backend — loads libaletheia-ffi.so via cgo + dlopen.
//
// This file uses cgo to call dlopen/dlsym from <dlfcn.h>. The GHC RTS
// is initialized exactly once per process (guarded by hsInitMu / hsInitDone,
// shared with renderer.go) and never finalized — hs_exit() is not supported
// for reinitialization.

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
//     uint32_t id, uint8_t ext, uint8_t dlc, uint8_t *data, uint8_t len,
//     uint8_t brs_present, uint8_t brs_value,
//     uint8_t esi_present, uint8_t esi_value) {
//     return ((char* (*)(void*, uint64_t, uint32_t, uint8_t, uint8_t,
//                         uint8_t*, uint8_t,
//                         uint8_t, uint8_t, uint8_t, uint8_t))fn)(
//         state, ts, id, ext, dlc, data, len,
//         brs_present, brs_value, esi_present, esi_value);
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
// //
// // Why strdup() rather than passing &args directly to hs_init:
// //   per the GHC user's guide §16.2 / Haskell-side "GHC.RTS.startupHaskell",
// //   hs_init's contract is that argv pointers MAY be retained for the
// //   process lifetime — the runtime parses +RTS flags lazily, and some
// //   bookkeeping (e.g. the stored program name returned by getProgName)
// //   keeps a live reference to the original strings.  Stack-allocated or
// //   Go-managed memory would not be safe across the hs_init return.
// //
// // Why we never free():
// //   (a) The retention window is the entire process lifetime — GHC has no
// //       hs_release_argv hook and no documented point at which the strings
// //       become unreachable.
// //   (b) The leak is bounded — exactly four small heap blocks
// //       ("aletheia" / "+RTS" / "-N<cores>" / "-RTS"), allocated once per
// //       process at first FFIBackend.Init() call (see lazyInit() guard
// //       below).  Total ~40 bytes, no growth.
// //   (c) Cross-binding parity — Python's `aletheia/_ffi.py` and C++'s
// //       `cpp/src/ffi_backend.cpp` both follow the same one-shot retain-
// //       forever pattern with the same rationale.  Diverging here would
// //       complicate the cross-binding leak audit (RUNBOOK.md §4 describes
// //       the expected steady-state RSS profile).
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
//     // Per the multi-line rationale above: bounded one-shot leak, retained
//     // for hs_init's documented argv lifetime; not freed.
// }
import "C"

import (
	"context"
	"fmt"
	"log/slog"
	"math"
	"path/filepath"
	"runtime"
	"strings"
	"sync"
	"sync/atomic"
	"unsafe"
)

var (
	hsInitMu    sync.Mutex
	hsInitDone  bool
	hsInitCores int

	// stablePtrCount tracks the live count of Haskell StablePtrs handed out
	// via aletheia_init across the process.  Incremented in [FFIBackend.Init]
	// and decremented in [FFIBackend.Close].  Exposed via [StablePtrCount]
	// for AGENTS.md cat 27 long-run leak detection — a non-zero value at the
	// end of a stability run indicates an unmatched Init/Close pair.
	stablePtrCount atomic.Int64
)

// hsInitialized reports whether the GHC RTS has been initialized (by an
// FFIBackend constructor). The rational renderer checks this before calling
// the kernel: FFI calls require the RTS to be up, so the renderer is vocal
// (returns an error) rather than self-initialising when it is not. Reads the
// shared hsInitDone under hsInitMu (a plain bool, not atomic).
func hsInitialized() bool {
	hsInitMu.Lock()
	defer hsInitMu.Unlock()
	return hsInitDone
}

// StablePtrCount returns the current number of live Haskell StablePtrs
// allocated via [FFIBackend.Init] and not yet released by
// [FFIBackend.Close].  Used by the long-run stability harness
// (`go/benchmarks/stability/main.go`) to detect leaks; production code does
// not need to call this.  Counter is shared across all FFIBackend instances
// in the process.
func StablePtrCount() int64 {
	return stablePtrCount.Load()
}

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
	formatDBCFn         unsafe.Pointer
	extractSignalsFn    unsafe.Pointer
	buildFrameBinFn     unsafe.Pointer
	updateFrameBinFn    unsafe.Pointer
	extractSignalsBinFn unsafe.Pointer
	freeBufFn           unsafe.Pointer
	freeStrFn           unsafe.Pointer
	closeFn             unsafe.Pointer
}

func (*FFIBackend) backend() {}

// loadSym looks up a symbol inside an already-dlopened library handle,
// returning a structured error (with dlerror text) if the symbol is
// missing. Callers cast the resulting void* to the expected C function
// pointer type before invoking it.
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
	// Reject NUL bytes before C.CString silently truncates.
	// filepath.Clean does not validate NUL; a NUL-bearing
	// libPath would translate to a different on-disk path inside cgo.
	if strings.ContainsRune(libPath, 0) {
		return nil, validationError("libPath contains NUL byte")
	}
	// Register the user's libPath so the lazy-loaded
	// Rational renderer (renderer.go) prefers the same .so instead of
	// falling back to its relative-path heuristic.  Production users
	// who pass an explicit libPath to NewFFIBackend
	// now have their choice honored by the renderer.
	RegisterDefaultLibPath(libPath)
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
	// loadSym calls below — a drifted comment is a bug).
	// `aletheia_format_rational` is not loaded here: the cross-binding
	// Rational pretty-printer is reached via the lazy-load in
	// `renderer.go`, independent of FFIBackend, so tests that never
	// instantiate a backend still route through the same Agda kernel
	// function.
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
	formatDBCFn, err := loadSym(handle, "aletheia_format_dbc")
	if err != nil {
		return nil, err
	}
	extractSignalsFn, err := loadSym(handle, "aletheia_extract_signals")
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
		formatDBCFn:         formatDBCFn,
		extractSignalsFn:    extractSignalsFn,
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
	stablePtrCount.Add(1)
	return state, nil
}

// Process sends a JSON command and returns the JSON response.
//
// Rejects oversize JSON payloads (`> MaxJSONBytes`) with a typed
// *InputBoundExceededError before marshaling across cgo, per AGENTS.md
// universal rule "Adversarial-input bounds at parser surfaces".  The
// Agda kernel enforces the same bound; this is the Go binding's
// short-circuit so we do not strdup a 100 MiB payload only to be
// rejected on the other side.
func (b *FFIBackend) Process(state unsafe.Pointer, input string) (string, error) {
	if len(input) > MaxJSONBytes {
		return "", newInputBoundExceededError(
			BoundKindInputLengthBytes,
			uint64(len(input)),
			MaxJSONBytes,
			CodeInputBoundExceeded,
		)
	}
	// Reject embedded NUL bytes before C.CString truncates.
	// The Agda parser is byte-oriented (not C-string-
	// oriented); a NUL-bearing input would silently truncate at the FFI
	// boundary.  The bound check above is bytes-of-Go-string, so the
	// post-truncation length disagreement is otherwise undetectable.
	if strings.IndexByte(input, 0) >= 0 {
		return "", validationError("input contains NUL byte")
	}

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
// bypassing JSON serialization on the input side.  The optional BRS and
// ESI CAN-FD bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) are encoded as
// (present, value) byte pairs — pass nil for CAN 2.0B frames.
func (b *FFIBackend) SendFrameBinary(
	state unsafe.Pointer, ts Timestamp,
	id CANID, dlc DLC, data []byte,
	brs *bool, esi *bool,
) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	if ts.Microseconds < 0 {
		return "", validationError("timestamp must be non-negative")
	}

	if len(data) > MaxFrameByteCount {
		return "", validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (%d)", len(data), MaxFrameByteCount))
	}

	var dataPtr *C.uint8_t
	if len(data) > 0 {
		dataPtr = (*C.uint8_t)(unsafe.Pointer(&data[0]))
	}

	brsPresent, brsValue := encodeMaybeBool(brs)
	esiPresent, esiValue := encodeMaybeBool(esi)

	// C.uint8_t(len(data)) is safe: the bounds check above guarantees
	// len(data) <= MaxFrameByteCount < 256, so the cast never truncates.
	result := C.call_send_frame(
		b.sendFrameFn, state,
		C.uint64_t(ts.Microseconds),
		C.uint32_t(id.Value()),
		ext,
		C.uint8_t(dlc.Value()),
		dataPtr,
		C.uint8_t(len(data)),
		brsPresent, brsValue,
		esiPresent, esiValue,
	)
	runtime.KeepAlive(data)
	if result == nil {
		return "", ffiError("aletheia_send_frame returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// encodeMaybeBool encodes an Optional[bool] as the (present, value) byte
// pair used by the binary FFI for CAN-FD BRS / ESI metadata.  Inverse of
// the Haskell shim's mkMaybeBool — nil → (0, 0); &false → (1, 0);
// &true → (1, 1).
func encodeMaybeBool(b *bool) (C.uint8_t, C.uint8_t) {
	if b == nil {
		return 0, 0
	}
	if *b {
		return 1, 1
	}
	return 1, 0
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
func (b *FFIBackend) SendRemoteBinary(state unsafe.Pointer, ts Timestamp, id CANID) (string, error) {
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

// FormatDBCBinary returns the loaded DBC as JSON via the binary FFI entry point.
func (b *FFIBackend) FormatDBCBinary(state unsafe.Pointer) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	result := C.call_format_dbc(b.formatDBCFn, state)
	if result == nil {
		return "", ffiError("aletheia_format_dbc returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// ExtractSignalsBinary extracts signals from a binary CAN frame via the binary FFI entry point.
func (b *FFIBackend) ExtractSignalsBinary(state unsafe.Pointer, id CANID, dlc DLC, data []byte) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	if len(data) > MaxFrameByteCount {
		return "", validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (%d)", len(data), MaxFrameByteCount))
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
	runtime.KeepAlive(data)
	if result == nil {
		return "", ffiError("aletheia_extract_signals returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// BuildFrameBin builds a CAN frame returning raw payload bytes, bypassing JSON entirely.
func (b *FFIBackend) BuildFrameBin(state unsafe.Pointer, id CANID, dlc DLC, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error) {
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
		n := int(numSignals)
		if len(indices) < n || len(nums) < n || len(dens) < n {
			return nil, validationError(fmt.Sprintf("parallel arrays too short for numSignals=%d: indices=%d nums=%d dens=%d", n, len(indices), len(nums), len(dens)))
		}
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
	// Defensive against future inliner / GC: keep the Go-side slices alive
	// until after the cgo call returns.  Without these, a sufficiently
	// aggressive inliner could observe that `indices`/`nums`/`dens`/`outBuf`
	// are no longer referenced from Go after their pointers cross the cgo
	// boundary, and the GC could reclaim them while the C code is still
	// reading.
	runtime.KeepAlive(indices)
	runtime.KeepAlive(nums)
	runtime.KeepAlive(dens)
	runtime.KeepAlive(outBuf)
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
func (b *FFIBackend) UpdateFrameBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte, numSignals uint32, indices []uint32, nums []int64, dens []int64) ([]byte, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	// Cap at the CAN-FD maximum payload size; every other data-accepting
	// method (SendFrameBinary, ExtractSignalsBinary) applies the same bound
	// before taking &data[0] into cgo.
	if len(data) > MaxFrameByteCount {
		return nil, validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (%d)", len(data), MaxFrameByteCount))
	}

	var dataPtr *C.uint8_t
	if len(data) > 0 {
		dataPtr = (*C.uint8_t)(unsafe.Pointer(&data[0]))
	}

	var indicesPtr *C.uint32_t
	var numsPtr *C.int64_t
	var densPtr *C.int64_t
	if numSignals > 0 {
		n := int(numSignals)
		if len(indices) < n || len(nums) < n || len(dens) < n {
			return nil, validationError(fmt.Sprintf("parallel arrays too short for numSignals=%d: indices=%d nums=%d dens=%d", n, len(indices), len(nums), len(dens)))
		}
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
	runtime.KeepAlive(data)
	runtime.KeepAlive(indices)
	runtime.KeepAlive(nums)
	runtime.KeepAlive(dens)
	runtime.KeepAlive(outBuf)
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
func (b *FFIBackend) ExtractSignalsBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte) ([]byte, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	var ext C.uint8_t
	if id.IsExtended() {
		ext = 1
	}

	// Cap at the CAN-FD maximum payload size; every other data-accepting
	// method applies the same bound before taking &data[0] into cgo.
	if len(data) > MaxFrameByteCount {
		return nil, validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (%d)", len(data), MaxFrameByteCount))
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
	runtime.KeepAlive(data)
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
	stablePtrCount.Add(-1)
}

// Compile-time assertion that *FFIBackend satisfies the Backend interface.
// Mirrors the !cgo branch in ffi_nocgo.go so interface signature drift fails
// at `go build` rather than at the first downstream caller.
var _ Backend = (*FFIBackend)(nil)
