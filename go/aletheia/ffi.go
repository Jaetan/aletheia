package aletheia

// FFI backend — loads libaletheia-ffi.so via cgo + dlopen.
//
// This file uses cgo to call dlopen/dlsym from <dlfcn.h>. The GHC RTS
// is initialized exactly once per process (via sync.Once) and never
// finalized — hs_exit() is not supported for reinitialization.

// #cgo LDFLAGS: -ldl
//
// #include <dlfcn.h>
// #include <stdlib.h>
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
import "C"

import (
	"runtime"
	"sync"
	"unsafe"
)

var hsInitOnce sync.Once

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
	handle    unsafe.Pointer // dlopen handle
	initFn    unsafe.Pointer
	processFn unsafe.Pointer
	freeStrFn unsafe.Pointer
	closeFn   unsafe.Pointer
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
func NewFFIBackend(libPath string) (*FFIBackend, error) {
	cPath := C.CString(libPath)
	defer C.free(unsafe.Pointer(cPath))

	handle := C.dlopen(cPath, C.RTLD_NOW|C.RTLD_LOCAL)
	if handle == nil {
		return nil, ffiError("dlopen failed: " + C.GoString(C.dlerror()))
	}

	hsInit, err := loadSym(handle, "hs_init")
	if err != nil {
		C.dlclose(handle)
		return nil, err
	}
	initFn, err := loadSym(handle, "aletheia_init")
	if err != nil {
		C.dlclose(handle)
		return nil, err
	}
	processFn, err := loadSym(handle, "aletheia_process")
	if err != nil {
		C.dlclose(handle)
		return nil, err
	}
	freeStrFn, err := loadSym(handle, "aletheia_free_str")
	if err != nil {
		C.dlclose(handle)
		return nil, err
	}
	closeFn, err := loadSym(handle, "aletheia_close")
	if err != nil {
		C.dlclose(handle)
		return nil, err
	}

	// Initialize GHC RTS exactly once per process.
	hsInitOnce.Do(func() {
		runtime.LockOSThread()
		defer runtime.UnlockOSThread()
		C.call_hs_init(hsInit, nil, nil)
	})

	return &FFIBackend{
		handle:    handle,
		initFn:    initFn,
		processFn: processFn,
		freeStrFn: freeStrFn,
		closeFn:   closeFn,
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

// Close finalizes and frees the session state.
func (b *FFIBackend) Close(state unsafe.Pointer) {
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	C.call_close(b.closeFn, state)
}
