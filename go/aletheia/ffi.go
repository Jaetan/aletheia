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
	"fmt"
	"log/slog"
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
	handle      unsafe.Pointer // dlopen handle
	initFn      unsafe.Pointer
	processFn   unsafe.Pointer
	sendFrameFn unsafe.Pointer
	freeStrFn   unsafe.Pointer
	closeFn     unsafe.Pointer
}

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

	// Required symbols from libaletheia-ffi.so:
	//   hs_init           — GHC RTS initialization (called once per process)
	//   aletheia_init     — create a new session (returns StablePtr)
	//   aletheia_process  — send JSON command, receive JSON response
	//   aletheia_send_frame — binary frame entry point (bypasses JSON input)
	//   aletheia_free_str — free Haskell-allocated response strings
	//   aletheia_close    — finalize and free session state
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
	hsInitMu.Lock()
	if !hsInitDone {
		if cfg.rtsCores > 1 {
			C.call_hs_init_rts(hsInit, C.int(cfg.rtsCores))
		} else {
			C.call_hs_init(hsInit, nil, nil)
		}
		hsInitCores = cfg.rtsCores
		hsInitDone = true
	} else if cfg.rtsCores != hsInitCores {
		slog.Warn("GHC RTS already initialized; ignoring WithRTSCores",
			"active_cores", hsInitCores,
			"requested_cores", cfg.rtsCores)
	}
	hsInitMu.Unlock()

	closeOnErr = false
	return &FFIBackend{
		handle:      handle,
		initFn:      initFn,
		processFn:   processFn,
		sendFrameFn: sendFrameFn,
		freeStrFn:   freeStrFn,
		closeFn:     closeFn,
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

// Close finalizes and frees the session state.
func (b *FFIBackend) Close(state unsafe.Pointer) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	C.call_close(b.closeFn, state)
}
