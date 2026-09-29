//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// The FFI backend: libaletheia-ffi.so, opened with dlopen through cgo. The
// GHC runtime starts once per process, under hsInitMu and hsInitDone, which
// this file shares with renderer.go, and is never finalised, since hs_exit
// does not allow a second start.

// #cgo LDFLAGS: -ldl
//
// #include <dlfcn.h>
// #include <stdint.h>
// #include <stdio.h>
// #include <stdlib.h>
// #include <string.h>
//
// #include "aletheia_abi.h"
//
// // cgo cannot call through a C function pointer, so each entry point gets a
// // typed trampoline. Go memory handed to C may hold no Go pointer, so a
// // structure crosses from Go with its pointer fields empty and the Go
// // pointers beside it; the trampoline fills a copy on its own stack, which
// // lives only for the call.
//
// static uint32_t call_abi_version(void *fn) {
//     return ((uint32_t (*)(void))fn)();
// }
// static void* call_init(void *fn) {
//     return ((void* (*)(void))fn)();
// }
// static char* call_process(void *fn, void *state, const struct aletheia_text *input) {
//     return ((char* (*)(void*, const struct aletheia_text*))fn)(state, input);
// }
// static void call_free_str(void *fn, char *ptr) {
//     ((void (*)(char*))fn)(ptr);
// }
// static void call_close(void *fn, void *state) {
//     ((void (*)(void*))fn)(state);
// }
// static char* call_send_frame(void *fn, void *state, struct aletheia_frame frame,
//     const uint8_t *data) {
//     frame.data = data;
//     return ((char* (*)(void*, const struct aletheia_frame*))fn)(state, &frame);
// }
// static char* call_send_error(void *fn, void *state, struct aletheia_frame frame) {
//     return ((char* (*)(void*, const struct aletheia_frame*))fn)(state, &frame);
// }
// static char* call_send_remote(void *fn, void *state, struct aletheia_frame frame) {
//     return ((char* (*)(void*, const struct aletheia_frame*))fn)(state, &frame);
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
// static char* call_extract_signals(void *fn, void *state, struct aletheia_frame frame,
//     const uint8_t *data) {
//     frame.data = data;
//     return ((char* (*)(void*, const struct aletheia_frame*))fn)(state, &frame);
// }
// // build_frame_bin and update_frame_bin share one shape. The kernel writes
// // into the Go buffer outData through the trampoline's copy of out, and only
// // the error and the count written travel back into out.
// static int8_t call_frame_bin(void *fn, void *state, struct aletheia_frame frame,
//     const uint8_t *data, struct aletheia_signal_values values,
//     const uint32_t *indices, const int64_t *nums, const int64_t *dens,
//     struct aletheia_buffer *out, uint8_t *outData) {
//     frame.data = data;
//     values.indices = indices;
//     values.numerators = nums;
//     values.denominators = dens;
//     struct aletheia_buffer buf = {outData, NULL, out->size};
//     int8_t status = ((int8_t (*)(void*, const struct aletheia_frame*,
//                                  const struct aletheia_signal_values*,
//                                  struct aletheia_buffer*))fn)(state, &frame, &values, &buf);
//     out->err = buf.err;
//     out->size = buf.size;
//     return status;
// }
// // The kernel allocates the result in C memory, so out is written directly.
// static int8_t call_extract_signals_bin(void *fn, void *state, struct aletheia_frame frame,
//     const uint8_t *data, struct aletheia_buffer *out) {
//     frame.data = data;
//     return ((int8_t (*)(void*, const struct aletheia_frame*,
//                         struct aletheia_buffer*))fn)(state, &frame, out);
// }
// static void call_free_buf(void *fn, uint8_t *ptr) {
//     ((void (*)(uint8_t*))fn)(ptr);
// }
//
// // The runtime's argument vector, assembled by rtsInitArgv in rts.go, moves
// // into storage C owns: hs_init_with_rtsopts may keep the array and its
// // strings for the life of the process, and cgo forbids C to keep a Go
// // pointer past the call. Nothing frees them, because the runtime offers no
// // hook to release them and the leak is one small array and a few short
// // strings, allocated once. The Python, C++ and Rust bindings retain theirs
// // the same way (aletheia/client/_ffi.py, cpp/src/ffi_backend.cpp,
// // rust/src/backend.rs).
// static char** g_alloc_argv(int n) {
//     return (char**)calloc((size_t)n, sizeof(char*));
// }
// static void g_set_argv(char **argv, int i, char *s) {
//     argv[i] = s;  // s is a CString the Go caller means to leak
// }
// static void call_hs_init_argv(void *fn, int argc, char **argv) {
//     // hs_init_with_rtsopts takes int* and char***; it may rewrite the local
//     // copies, stripping the span it consumed, and those copies are discarded.
//     ((void (*)(int*, char***))fn)(&argc, &argv);
// }
import "C"

import (
	"context"
	"fmt"
	"log/slog"
	"math"
	"os"
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

	// stablePtrCount is how many session handles the process has taken from
	// the kernel and not yet given back: [FFIBackend.Init] adds one and
	// [FFIBackend.Close] takes one away.
	stablePtrCount atomic.Int64
)

// hsInitialized reports whether a backend has started the GHC runtime. The
// rational renderer asks before calling the kernel, so that it can answer an
// error rather than start the runtime itself.
func hsInitialized() bool {
	hsInitMu.Lock()
	defer hsInitMu.Unlock()
	return hsInitDone
}

// StablePtrCount is how many sessions the process holds open across every
// backend: the handles [FFIBackend.Init] took and [FFIBackend.Close] has not
// released. The long-run stability benchmark reads it to see a leak; nothing
// in production needs it.
func StablePtrCount() int64 {
	return stablePtrCount.Load()
}

// FFIBackend is the [Backend] that calls libaletheia-ffi.so, opened with
// dlopen. It needs Linux, for dlfcn, cgo, for the loader, and the library
// built from the kernel. The GHC runtime starts once per process (rts.go) and
// is never finalised, and every call into it runs on a pinned OS thread,
// because the runtime keeps state per capability.
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

// loadSym resolves one symbol of an opened library, with the loader's own
// message on failure. The caller pins the thread, since dlerror is per thread.
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

// NewFFIBackendFromEnv opens the library named by ALETHEIA_LIB, which is what
// a bundled install exports, as the Python and Rust bindings also do. An
// unset or empty variable is a validation error; to name the path, use
// [NewFFIBackend].
func NewFFIBackendFromEnv(opts ...FFIBackendOption) (*FFIBackend, error) {
	libPath := os.Getenv("ALETHEIA_LIB")
	if libPath == "" {
		return nil, validationError(
			"ALETHEIA_LIB is not set: set it to the path of libaletheia-ffi.so, or use NewFFIBackend(path)")
	}
	return NewFFIBackend(libPath, opts...)
}

// NewFFIBackend opens libaletheia-ffi.so at the path and starts the GHC
// runtime if no backend has. The handle is never closed on success, since the
// runtime owns threads that reference the library.
func NewFFIBackend(libPath string, opts ...FFIBackendOption) (*FFIBackend, error) {
	// dlerror is per thread, so the lookups below must not migrate.
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	libPath = filepath.Clean(libPath)
	// Clean does not reject a NUL, and C.CString would truncate at one,
	// opening a different path than the caller named.
	if strings.ContainsRune(libPath, 0) {
		return nil, validationError("libPath contains NUL byte")
	}
	// The renderer loads the library on its own; registering the path here
	// keeps it on the same one rather than its relative search.
	RegisterDefaultLibPath(libPath)
	cPath := C.CString(libPath)
	defer C.free(unsafe.Pointer(cPath))

	handle := C.dlopen(cPath, C.RTLD_NOW|C.RTLD_LOCAL)
	if handle == nil {
		return nil, ffiError("dlopen failed: " + C.GoString(C.dlerror()))
	}
	closeOnErr := true
	defer func() {
		if closeOnErr {
			C.dlclose(handle)
		}
	}()

	// The version first: a library laid out for another ABI is refused
	// before any other entry is resolved or its runtime is started.
	abiVersionFn, err := loadSym(handle, "aletheia_abi_version")
	if err != nil {
		return nil, err
	}
	if err := abiVersionError(uint32(C.call_abi_version(abiVersionFn))); err != nil {
		return nil, err
	}

	// aletheia_format_rational is deliberately not among these: the renderer
	// loads it lazily in renderer.go, so a test that never builds a backend
	// still renders through the kernel.
	hsInit, err := loadSym(handle, rtsInitSymbol)
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

	cfg := ffiConfig{rtsCores: 1}
	for _, o := range opts {
		o(&cfg)
	}
	if cfg.rtsCores < 1 {
		return nil, validationError(fmt.Sprintf("rtsCores must be >= 1, got %d", cfg.rtsCores))
	}
	if cfg.rtsCores > math.MaxInt32 {
		return nil, validationError(fmt.Sprintf("rtsCores %d exceeds C int range (max %d)", cfg.rtsCores, math.MaxInt32))
	}

	hsInitMu.Lock()
	defer hsInitMu.Unlock()
	if !hsInitDone {
		// The argument vector always carries the heap cap, whatever the core
		// count, so the host is contained either way. Its array and strings
		// are leaked on purpose, as the preamble explains.
		argv := rtsInitArgv(cfg.rtsCores)
		cargv := C.g_alloc_argv(C.int(len(argv)))
		for i, s := range argv {
			C.g_set_argv(cargv, C.int(i), C.CString(s))
		}
		C.call_hs_init_argv(hsInit, C.int(len(argv)), cargv)
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

// extFlag is the byte the wire takes for an extended identifier.
func extFlag(id CANID) C.uint8_t {
	if id.IsExtended() {
		return 1
	}
	return 0
}

// abiVersion is ALETHEIA_ABI_VERSION: the version of the structures and
// signatures this binding lays out, which the header test holds to the
// header's.
const abiVersion = 2

// abiVersionError refuses a library whose ABI version is not abiVersion.
func abiVersionError(found uint32) error {
	if found == abiVersion {
		return nil
	}
	return ffiError(fmt.Sprintf("the library implements ABI version %d, and this binding needs %d", found, abiVersion))
}

// abiField is one field of a structure the preamble declares, at its offset.
type abiField struct {
	name   string
	offset uintptr
}

// abiLayout answers the size and the fields, in declaration order, of each
// structure the preamble declares, for the test that holds them to the
// kernel's header.
func abiLayout() (sizes map[string]uintptr, fields map[string][]abiField) {
	var t C.struct_aletheia_text
	var f C.struct_aletheia_frame
	var v C.struct_aletheia_signal_values
	var b C.struct_aletheia_buffer
	var r C.struct_aletheia_rational
	var d C.struct_aletheia_decimal
	sizes = map[string]uintptr{
		"aletheia_text":          unsafe.Sizeof(t),
		"aletheia_frame":         unsafe.Sizeof(f),
		"aletheia_signal_values": unsafe.Sizeof(v),
		"aletheia_buffer":        unsafe.Sizeof(b),
		"aletheia_rational":      unsafe.Sizeof(r),
		"aletheia_decimal":       unsafe.Sizeof(d),
	}
	fields = map[string][]abiField{
		"aletheia_text": {
			{"data", unsafe.Offsetof(t.data)},
			{"size", unsafe.Offsetof(t.size)},
		},
		"aletheia_frame": {
			{"timestamp", unsafe.Offsetof(f.timestamp)},
			{"data", unsafe.Offsetof(f.data)},
			{"can_id", unsafe.Offsetof(f.can_id)},
			{"extended", unsafe.Offsetof(f.extended)},
			{"dlc", unsafe.Offsetof(f.dlc)},
			{"data_len", unsafe.Offsetof(f.data_len)},
			{"brs_present", unsafe.Offsetof(f.brs_present)},
			{"brs_value", unsafe.Offsetof(f.brs_value)},
			{"esi_present", unsafe.Offsetof(f.esi_present)},
			{"esi_value", unsafe.Offsetof(f.esi_value)},
		},
		"aletheia_signal_values": {
			{"indices", unsafe.Offsetof(v.indices)},
			{"numerators", unsafe.Offsetof(v.numerators)},
			{"denominators", unsafe.Offsetof(v.denominators)},
			{"count", unsafe.Offsetof(v.count)},
		},
		"aletheia_buffer": {
			{"data", unsafe.Offsetof(b.data)},
			{"err", unsafe.Offsetof(b.err)},
			{"size", unsafe.Offsetof(b.size)},
		},
		"aletheia_rational": {
			{"numerator", unsafe.Offsetof(r.numerator)},
			{"denominator", unsafe.Offsetof(r.denominator)},
		},
		"aletheia_decimal": {
			{"value", unsafe.Offsetof(d.value)},
			{"err", unsafe.Offsetof(d.err)},
		},
	}
	return sizes, fields
}

// wireFrame is the frame's identifier, DLC and payload length, its pointer
// left empty for the trampoline to fill. The caller has bounded the payload,
// so its length fits the byte.
func wireFrame(id CANID, dlc DLC, data []byte) C.struct_aletheia_frame {
	return C.struct_aletheia_frame{
		can_id:   C.uint32_t(id.Value()),
		extended: extFlag(id),
		dlc:      C.uint8_t(dlc.Value()),
		data_len: C.uint8_t(len(data)),
	}
}

// framePayloadPtr bounds a payload at the CAN-FD maximum and returns the
// pointer the call takes, nil for an empty payload. The caller keeps the
// slice alive across the call.
func framePayloadPtr(data []byte) (*C.uint8_t, error) {
	if len(data) > MaxFrameByteCount {
		return nil, validationError(fmt.Sprintf("data length %d exceeds CAN-FD maximum (%d)", len(data), MaxFrameByteCount))
	}
	if len(data) == 0 {
		return nil, nil
	}
	return (*C.uint8_t)(unsafe.Pointer(&data[0])), nil
}

// signalArrays splits one slice of injections into the three parallel arrays
// the C entry point takes. That shape exists here and nowhere else: the
// interface above carries one slice, and this is the file that talks to C.
func signalArrays(signals []SignalInjection) (indices []uint32, nums, dens []int64) {
	indices = make([]uint32, len(signals))
	nums = make([]int64, len(signals))
	dens = make([]int64, len(signals))
	for i, s := range signals {
		indices[i] = s.Index
		nums[i] = s.Numerator
		dens[i] = s.Denominator
	}
	return indices, nums, dens
}

// signalArrayPtrs is the head of each array, or three nulls for an empty
// injection list. The three are built together by signalArrays above, so they
// are the same length by construction and there is nothing here to check.
func signalArrayPtrs(indices []uint32, nums, dens []int64) (*C.uint32_t, *C.int64_t, *C.int64_t) {
	if len(indices) == 0 {
		return nil, nil, nil
	}
	return (*C.uint32_t)(unsafe.Pointer(&indices[0])),
		(*C.int64_t)(unsafe.Pointer(&nums[0])),
		(*C.int64_t)(unsafe.Pointer(&dens[0]))
}

// stringResult copies a response the kernel allocated and frees it. A null
// answer is the kernel or the ABI malfunctioning, never an ordinary refusal,
// which arrives as an error envelope in the string.
func (b *FFIBackend) stringResult(symbol string, result *C.char) (string, error) {
	if result == nil {
		return "", ffiError(symbol + " returned null")
	}
	defer C.call_free_str(b.freeStrFn, result)
	return C.GoString(result), nil
}

// binaryStatusError is the error a non-zero status carries, freeing the
// message the kernel allocated for it.
func (b *FFIBackend) binaryStatusError(symbol string, status C.int8_t, outErr *C.char) error {
	if outErr != nil {
		msg := C.GoString(outErr)
		C.call_free_str(b.freeStrFn, outErr)
		return protocolError(msg)
	}
	return protocolError(fmt.Sprintf("%s returned status %d with null error message", symbol, status))
}

// Init opens a session and returns its handle, which the kernel owns.
func (b *FFIBackend) Init() (unsafe.Pointer, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	state := C.call_init(b.initFn)
	if state == nil {
		return nil, ffiError("aletheia_init returned null")
	}
	stablePtrCount.Add(1)
	return state, nil
}

// Process sends one JSON command and returns the JSON response. A payload
// past MaxJSONBytes is refused here, before it is copied across the boundary;
// the kernel bounds it too. The kernel reads every byte of input, and answers a
// NUL or bytes that are not UTF-8 with an ffi_validation_error response.
func (b *FFIBackend) Process(state unsafe.Pointer, input string) (string, error) {
	if len(input) > MaxJSONBytes {
		return "", newInputBoundExceededError(
			BoundKindInputLengthBytes,
			uint64(len(input)),
			MaxJSONBytes,
			CodeInputBoundExceeded,
		)
	}
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	cInput := C.CString(input)
	defer C.free(unsafe.Pointer(cInput))
	text := C.struct_aletheia_text{data: cInput, size: C.size_t(len(input))}

	return b.stringResult("aletheia_process", C.call_process(b.processFn, state, &text))
}

// SendFrameBinary sends a CAN frame without serialising it to JSON. The
// CAN-FD BRS and ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) cross as a
// present-and-value byte pair, both zero when the caller passes nil.
func (b *FFIBackend) SendFrameBinary(
	state unsafe.Pointer, ts Timestamp,
	id CANID, dlc DLC, data []byte,
	brs *bool, esi *bool,
) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	if ts.Microseconds < 0 {
		return "", validationError("timestamp must be non-negative")
	}
	dataPtr, err := framePayloadPtr(data)
	if err != nil {
		return "", err
	}
	brsPresent, brsValue := encodeMaybeBool(brs)
	esiPresent, esiValue := encodeMaybeBool(esi)

	frame := wireFrame(id, dlc, data)
	frame.timestamp = C.uint64_t(ts.Microseconds)
	frame.brs_present, frame.brs_value = brsPresent, brsValue
	frame.esi_present, frame.esi_value = esiPresent, esiValue
	result := C.call_send_frame(b.sendFrameFn, state, frame, dataPtr)
	runtime.KeepAlive(data)
	return b.stringResult("aletheia_send_frame", result)
}

// encodeMaybeBool writes an optional bool as the present-and-value pair the
// binary wire takes, which mkMaybeBool in the Haskell shim reads back: nil is
// (0, 0), false is (1, 0) and true is (1, 1).
func encodeMaybeBool(b *bool) (C.uint8_t, C.uint8_t) {
	if b == nil {
		return 0, 0
	}
	if *b {
		return 1, 1
	}
	return 1, 0
}

// SendErrorBinary sends a CAN error event.
func (b *FFIBackend) SendErrorBinary(state unsafe.Pointer, ts Timestamp) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	if ts.Microseconds < 0 {
		return "", validationError("timestamp must be non-negative")
	}
	return b.stringResult("aletheia_send_error",
		C.call_send_error(b.sendErrorFn, state, C.struct_aletheia_frame{timestamp: C.uint64_t(ts.Microseconds)}))
}

// SendRemoteBinary sends a CAN remote frame event.
func (b *FFIBackend) SendRemoteBinary(state unsafe.Pointer, ts Timestamp, id CANID) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	if ts.Microseconds < 0 {
		return "", validationError("timestamp must be non-negative")
	}
	return b.stringResult("aletheia_send_remote",
		C.call_send_remote(b.sendRemoteFn, state, C.struct_aletheia_frame{
			timestamp: C.uint64_t(ts.Microseconds),
			can_id:    C.uint32_t(id.Value()),
			extended:  extFlag(id),
		}))
}

// StartStreamBinary begins streaming mode.
func (b *FFIBackend) StartStreamBinary(state unsafe.Pointer) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	return b.stringResult("aletheia_start_stream", C.call_start_stream(b.startStreamFn, state))
}

// EndStreamBinary ends streaming mode and returns the verdicts.
func (b *FFIBackend) EndStreamBinary(state unsafe.Pointer) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	return b.stringResult("aletheia_end_stream", C.call_end_stream(b.endStreamFn, state))
}

// FormatDBCBinary returns the loaded DBC as JSON.
func (b *FFIBackend) FormatDBCBinary(state unsafe.Pointer) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	return b.stringResult("aletheia_format_dbc", C.call_format_dbc(b.formatDBCFn, state))
}

// ExtractSignalsBinary extracts the signals of a frame, answering JSON.
func (b *FFIBackend) ExtractSignalsBinary(state unsafe.Pointer, id CANID, dlc DLC, data []byte) (string, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	dataPtr, err := framePayloadPtr(data)
	if err != nil {
		return "", err
	}
	result := C.call_extract_signals(b.extractSignalsFn, state, wireFrame(id, dlc, data), dataPtr)
	runtime.KeepAlive(data)
	return b.stringResult("aletheia_extract_signals", result)
}

// BuildFrameBin builds a frame from signal values, answering raw payload
// bytes with no JSON on either side.
func (b *FFIBackend) BuildFrameBin(state unsafe.Pointer, id CANID, dlc DLC, signals []SignalInjection) ([]byte, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	return b.frameBin("build_frame_bin", b.buildFrameBinFn, state, wireFrame(id, dlc, nil), nil, dlc, signals)
}

// frameBin runs build_frame_bin or update_frame_bin, which differ only in the
// payload the frame carries, and answers the payload the kernel wrote.
func (b *FFIBackend) frameBin(
	symbol string, fn, state unsafe.Pointer,
	frame C.struct_aletheia_frame, dataPtr *C.uint8_t, dlc DLC, signals []SignalInjection,
) ([]byte, error) {
	indices, nums, dens := signalArrays(signals)
	indicesPtr, numsPtr, densPtr := signalArrayPtrs(indices, nums, dens)
	values := C.struct_aletheia_signal_values{count: C.uint32_t(len(signals))}
	outBuf := make([]byte, dlc.ToBytes())
	var outBufPtr *C.uint8_t
	if len(outBuf) > 0 {
		outBufPtr = (*C.uint8_t)(unsafe.Pointer(&outBuf[0]))
	}
	out := C.struct_aletheia_buffer{size: C.uint32_t(len(outBuf))}

	status := C.call_frame_bin(fn, state, frame, dataPtr, values,
		indicesPtr, numsPtr, densPtr, &out, outBufPtr)
	// Every slice whose pointer crossed stays alive until the call returns:
	// nothing in Go refers to them after the pointers are taken, so the
	// collector could otherwise reclaim one while the kernel reads it.
	runtime.KeepAlive(indices)
	runtime.KeepAlive(nums)
	runtime.KeepAlive(dens)
	runtime.KeepAlive(outBuf)
	if status != 0 {
		return nil, b.binaryStatusError(symbol, status, out.err)
	}
	return outBuf[:int(out.size)], nil
}

// UpdateFrameBin rewrites signals in an existing payload, answering raw
// payload bytes with no JSON on either side.
func (b *FFIBackend) UpdateFrameBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte, signals []SignalInjection) ([]byte, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	dataPtr, err := framePayloadPtr(data)
	if err != nil {
		return nil, err
	}
	result, err := b.frameBin("update_frame_bin", b.updateFrameBinFn, state, wireFrame(id, dlc, data), dataPtr, dlc, signals)
	runtime.KeepAlive(data)
	return result, err
}

// ExtractSignalsBin extracts signals as the packed binary the caller parses,
// with no JSON on either side.
func (b *FFIBackend) ExtractSignalsBin(state unsafe.Pointer, id CANID, dlc DLC, data []byte) ([]byte, error) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	dataPtr, err := framePayloadPtr(data)
	if err != nil {
		return nil, err
	}
	var out C.struct_aletheia_buffer
	status := C.call_extract_signals_bin(b.extractSignalsBinFn, state, wireFrame(id, dlc, data), dataPtr, &out)
	runtime.KeepAlive(data)
	if status != 0 {
		return nil, b.binaryStatusError("extract_signals_bin", status, out.err)
	}
	outBuf, outSize := out.data, out.size
	// The copy below takes a C int, which cannot hold every uint32.
	if outSize > math.MaxInt32 {
		C.call_free_buf(b.freeBufFn, outBuf)
		return nil, protocolError(fmt.Sprintf("extract_signals_bin returned outSize %d exceeding C.int range", outSize))
	}
	result := C.GoBytes(unsafe.Pointer(outBuf), C.int(outSize))
	C.call_free_buf(b.freeBufFn, outBuf)
	return result, nil
}

// Close ends the session and frees its state.
func (b *FFIBackend) Close(state unsafe.Pointer) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	C.call_close(b.closeFn, state)
	stablePtrCount.Add(-1)
}

// The interface is satisfied here as it is in the no-cgo file, so a drift in
// its signatures fails the build rather than the first caller.
var _ Backend = (*FFIBackend)(nil)
